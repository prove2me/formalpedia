-- Prove2me | Theorems.Thm_QMultiMean_proposition_3_2
-- name    : QMultiMean.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:26.247997+00:00
-- url     : https://prove2.me/theorems/a1336a5b-5b2f-42ca-bedb-2a8e10ce0db0
-- title:
--   Proposition 3.2 — directional mean oracle with $\tilde O(m\sqrt{L_2}\log^2(1/\epsilon))$ queries
-- statement:
--   Let $X$ be a finite random variable over $\mathbb R^d$ with $\|X\|_2\le1$. Let $L_2\in(0,1]$, let $m\ge1/L_2$ be an integer, let $\alpha,\epsilon\in(0,1)$, and assume $\mathbb E[\|X\|_2]\le L_2$. There is an oracle circuit with input register $\mathcal H_G$ whose unitary $\widetilde{\mathcal P}$ satisfies
--   $$\widetilde{\mathcal P}:|u\rangle|\vec0\rangle\mapsto|u\rangle|\varphi_u\rangle\qquad(u\in G),$$
--   with
--   $$\Big\||\varphi_u\rangle-e^{im\,\mathbb E[[\![\alpha\langle u,X\rangle]\!]_0^1]}|\vec 0\rangle\Big\|\le\epsilon$$
--   for at least a fraction $1-\alpha/2$ of the grid points $u\in G$. The circuit uses at most
--   $$C\,m\sqrt{L_2}\,\max\{1,\log(1/\epsilon)\}^2\,(1+\log(mL_2))^k$$
--   quantum experiments and binary oracle queries, for universal constants $C,k$. It is chosen from $d,L_2,m,\alpha,\epsilon$, $\Omega$ and $E$ only, and the guarantee holds for every quantum experiment and binary oracle of $X$.
--
--   This is the phase oracle to which Algorithm 1 applies the quantum Fourier transform over $G$.
--
--   Differences from the source:
--   - reading: an informal quantum estimator / algorithm using quantum experiments and binary oracle queries → an oracle circuit (unitary gates, calls to U_P, U_P⁻¹, B_X, B_X⁻¹ on copies of H_Ω⊗H_E, final computational-basis measurement, classical output map) chosen from the parameters, Ω and E before P, X and the oracles, and successful for every pair of unitaries meeting Definitions 2.5–2.6; reason: the paper defines no model of computation; this is the standard query model its proofs use, and the oracles are specified only on |0⟩ and |ω⟩|0⃗⟩
--   - reading: a unitary P̃ : |u⟩|0⃗⟩ ↦ |u⟩|φ_u⟩ acting on H_G ⊗ H_aux, implemented using Õ(m√L₂ log²(1/ϵ)) quantum experiments and binary oracle queries → the operator implemented by an oracle circuit with input register indexed by the grid, mapping |u⟩|0⃗⟩ to |u⟩|φ_u⟩ for every u, with at most C·m·√L₂·max(1, log(1/ϵ))²·(1 + log(mL₂))^k calls, C and k universal and chosen first; reason: H_aux is the circuit's workspace; the explicit count matches the proof's O((mL₂ + log(1/ϵ))·log(mL₂/ϵ)/√L₂) on p.10 using mL₂ ≥ 1
--   - reading: m ≥ 1/L₂ a real → m a natural number with m ≥ 1/L₂; reason: m indexes the grid G = {j/m − 1/2 + 1/(2m) : j ∈ {0, …, m−1}}^d, which needs an integer
--   - generalization: E ⊂ ℝ^d the finite support of X, with 0⃗ ∈ E assumed (Definitions 2.2, 2.6) → E any finite set containing 0 and every value X(ω); reason: the support together with 0 is one admissible E, so the statement specializes to the source's
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the natural log gives the weaker hypothesis n ≥ log(d/δ) and the smaller error bound, so it is the stronger reading; a base change is absorbed by the query constant
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.9–10, Proposition 3.2

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit
import Definitions.Def_QMultiMean_gridPoint

set_option autoImplicit false

namespace QMultiMean

open Classical in
/-- Proposition 3.2 (Directional mean oracle) of Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2,
p.9: let `X` be a `d`-dimensional random variable with `‖X‖₂ ≤ 1`. Given reals `L₂ ∈ (0, 1]`,
`m ≥ 1/L₂`, `α, ϵ ∈ (0, 1)` such that `E[‖X‖₂] ≤ L₂`, there is a unitary
`P̃ : |u⟩|0⃗⟩ ↦ |u⟩|φ_u⟩` on `H_G ⊗ H_aux`, implemented with `Õ(m√L₂ log²(1/ϵ))` quantum
experiments and binary oracle queries, such that `‖|φ_u⟩ − e^{imE[⟦α⟨u,X⟩⟧₀¹]}|0⃗⟩‖ ≤ ϵ` for a
fraction at least `1 − α/2` of all `u ∈ G`.

**Formalization Note.** The unitary is the operator implemented by an oracle circuit whose input
register is `H_G` (labels `Fin d → Fin m`) and whose gates are chosen from `d, L₂, m, α, ϵ, N, E`
before the instance; `H_aux` is the circuit's workspace (register copies and ancilla), `|0⃗⟩` its
all-zero label. Part (i), `|u⟩|0⃗⟩ ↦ |u⟩|φ_u⟩`, holds for every `u`. `Õ(·)` is made explicit with
universal constants `C, k` chosen first: `C·m·√L₂·max(1, log(1/ϵ))²·(1 + log(mL₂))^k` (natural log).
`m` is a natural number because it indexes the grid. `E` is any finite set containing `0` and the
values of `X`. -/
theorem proposition_3_2 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ (d : ℕ) (L₂ α ε : ℝ) (m : ℕ), 0 < L₂ → L₂ ≤ 1 → 1 / L₂ ≤ (m : ℝ) →
      0 < α → α < 1 → 0 < ε → ε < 1 →
      ∀ (N : ℕ) (E : Finset (Vec d)) (h0 : (0 : Vec d) ∈ E),
      ∃ Cir : OracleCircuit (Fin d → Fin m) N E,
        (Cir.T : ℝ) ≤ C * m * Real.sqrt L₂ * (max 1 (Real.log (1 / ε))) ^ 2 *
            (1 + Real.log (m * L₂)) ^ k ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P → (∀ ω, X ω ∈ E) →
          (∀ ω, ‖X ω‖ ≤ 1) → expect P (fun ω => ‖X ω‖) ≤ L₂ →
          ∀ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
            (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
            IsQuantumExperiment P U → IsBinaryOracle E h0 X B →
            ∃ φ : (Fin d → Fin m) → AuxLabel N E Cir.r Cir.A → ℂ,
              (∀ (u u' : Fin d → Fin m) (y : AuxLabel N E Cir.r Cir.A),
                Cir.implemented U B (u', y) (u, initAux h0 Cir.r Cir.A) =
                  if u' = u then φ u y else 0) ∧
              (1 - α / 2) * (m : ℝ) ^ d ≤
                ((Finset.univ.filter (fun u : Fin d → Fin m =>
                  cnorm (fun y => φ u y -
                    (if y = initAux h0 Cir.r Cir.A then
                      Complex.exp (Complex.I * ((m : ℝ) *
                        expect P (fun ω => truncR 0 1 (α * inner ℝ (gridPoint m u) (X ω)))))
                    else 0)) ≤ ε)).card : ℝ) := by sorry

end QMultiMean
