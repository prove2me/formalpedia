-- Prove2me | Theorems.Thm_SysBathGibbs_theorem_6_7
-- name    : SysBathGibbs.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:09.712903+00:00
-- url     : https://prove2.me/theorems/bf5f024a-53bf-43fd-b20a-12ee1097bcb6
-- title:
--   Theorem 6.7 — Gibbs-centered sums of coefficient-quasi-local maps
-- statement:
--   For all $C_0,c_0>0$ there are $C,C'>0$, depending only on $\beta,q,C_0,c_0$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites, every uniformly coefficient-quasi-local family $(\mathcal A_x)_{x\in[n]}$ with constants $C_0,c_0$ and $\langle\mathbf 1,\mathcal A_x(\mathbf 1)\rangle_{\rho_\beta}=0$ for every $x$, and every $O$,
--   $$
--   \Big\|\sum_x\mathcal A_x(O)\Big\|^2_{\rho_\beta}\le Cn\big(\mathcal E_K(O)+\|O\|^2_{\rho_\beta}\big)\le C'n\big(\mathcal E_K(O)+|\operatorname{Tr}(\rho_\beta O)|^2\big).
--   $$
--
--   This is the field bound of the paper: a sum of $n$ Gibbs-centered quasi-local terms has squared weighted norm $O(n)$ rather than $O(n^2)$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - encoding: the maps A_x of (6.5) → ℂ-linear maps on matrices; reason: the superoperators of the paper are linear
--   - reading: "the constants depend only on β, q, and the constants in (6.5)" → ∀ C0 c0 > 0, ∃ C C′ > 0, before n, the chain and the family; reason: the literal dependence
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Theorem 6.7 (eq. (6.12)), p.49

import Definitions.Def_SysBathGibbs_Coefficient

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Theorem 6.7 (Gibbs-centered sums of coefficient-quasi-local maps)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.49.
If `(A_x)` is uniformly coefficient-quasi-local and `⟨1, A_x(1)⟩_{ρ_β} = 0` for every `x`, then for every
`O`, `‖∑_x A_x(O)‖² ≤ Cn(E_K(O) + ‖O‖²) ≤ C′n(E_K(O) + |Tr(ρ_β O)|²)`, with `C, C′` depending only on
`β, q` and the constants in (6.5).

**Formalization Note.** `A_x` is a linear map, as every map of `A(S)` and each limit of such maps is. -/
theorem theorem_6_7 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q → ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
      ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ A : Fin n → (SysMat n q →ₗ[ℂ] SysMat n q),
            IsCoefQuasiLocal β (chainHam h) C₀ c₀ (fun x => A x) →
            (∀ x, kmsInner β (chainHam h) 1 (A x 1) = 0) →
            ∀ O : SysMat n q,
              kmsNorm β (chainHam h) (∑ x, A x O) ^ 2 ≤
                C * n * (pauliEnergy β (chainHam h) O + kmsNorm β (chainHam h) O ^ 2) ∧
              C * n * (pauliEnergy β (chainHam h) O + kmsNorm β (chainHam h) O ^ 2) ≤
                C' * n * (pauliEnergy β (chainHam h) O +
                  ‖Matrix.trace (gibbs β (chainHam h) * O)‖ ^ 2) := by sorry

end SysBathGibbs
