-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_fact_1
-- name    : QuantumWalkSearch.ApproxRAA.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:49.153992+00:00
-- url     : https://prove2.me/theorems/e4ed85a6-3341-405a-9a98-fc8fb77d01dd
-- title:
--   Fact 1 — the error operator Eᵢ = Rᵢ − ref(φ_{i−1}) kills |φ_{i−1}⟩ and has norm ≤ βᵢ on states with clean registers K_i, …, K_T
-- statement:
--   Let $|\pi\rangle\in\mathcal H$ be a unit vector, let $\gamma>0$ be the precision parameter, $\beta_i=\frac{18}{4\pi^3}\gamma/i^2$, and let the circuits $R_i$ be unitary with $R_i|\pi\rangle|0\rangle=|\pi\rangle|0\rangle$ and $\|(R_i+\mathrm{Id})|\psi\rangle|0\rangle\|\le\beta_i\|\psi\|$ for $\langle\pi|\psi\rangle=0$. Consider Approximate RAA with $T$ registers, and for $1\le i\le T$ let $E_i=R_i-\mathrm{ref}(\varphi_{i-1})$ be its error operator at level $i$. Then
--
--   1. $E_i|\varphi_{i-1}\rangle=0$, and
--   2. for every vector $v=|\psi\rangle|0^{S_i}\rangle$, where $|\psi\rangle\in\mathcal H\otimes[\bigotimes_{j=1}^{i-1}K_j]$ and the registers $K_i,\dots,K_T$ are in $|0\rangle$, with $v\perp|\varphi_{i-1}\rangle$,
--   $$
--   \|E_i\,v\|\le\beta_i\,\|v\|.
--   $$
--
--   The fact says that steps 3–5 of Approximate RAA implement the ideal reflection $\mathrm{ref}(\varphi_{i-1})$ up to error $\beta_i$ on the states the algorithm can reach; it is the input of the one-level amplitude bound.
--
--   **Formalization Note** The level is indexed by $ii=i-1$ (a `Fin T`), and the condition "$K_i,\dots,K_T$ are in $|0\rangle$" says that $v$ vanishes on every basis state in which some register of $0$-based index $j\ge ii$ is not zero. The bound is the homogeneous form of the paper's "$\le\beta_i$" for states.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 12, Fact 1 (proof of Lemma 1)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

namespace QuantumWalkSearch.ApproxRAA

/-- Fact 1 (p. 12). For a precision parameter `γ > 0` and step `i = ii + 1` of Approximate
RAA with `T` registers, the error
operator `E_i = R_i − ref(φ_{i−1})` satisfies
1. `E_i |φ_{i−1}⟩ = 0`;
2. `‖E_i v‖ ≤ β_i ‖v‖` for every `v = |ψ⟩|0^{S_i}⟩` (the registers `K_i, …, K_T`, 0-based
   indices `j ≥ ii`, are all zero) orthogonal to `|φ_{i−1}⟩`. -/
theorem fact_1 {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T : ℕ) (ii : Fin T) :
    act (errOp M z R piState T ii) (phi M z R piState T ii.val) = 0 ∧
    ∀ v : EuclideanSpace ℂ (X × X × Regs κ T),
      (∀ p : X × X × Regs κ T, (∃ j : Fin T, ii ≤ j ∧ p.2.2 j ≠ z (j.val + 1)) → v p = 0) →
      inner ℂ (phi M z R piState T ii.val) v = 0 →
      ‖act (errOp M z R piState T ii) v‖ ≤ beta γ (ii.val + 1) * ‖v‖ := by sorry

end QuantumWalkSearch.ApproxRAA
