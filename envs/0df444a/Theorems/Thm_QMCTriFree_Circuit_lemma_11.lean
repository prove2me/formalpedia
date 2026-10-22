-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_11
-- name    : QMCTriFree.Circuit.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:39.350254+00:00
-- url     : https://prove2.me/theorems/3f1e865b-7099-4217-bb96-d27f7cf215f2
-- title:
--   Lemma 11 — equatorial $P_k$: $\langle v_k|P_k|v_k\rangle=0$, $P_k$ flips the Bloch vector, and the phase $\gamma_{ij}$ is uniform
-- statement:
--   Let $\vec v\in S^2$ be a Bloch vector, $\vec n\in S^2$ with $\vec n\cdot\vec v=0$, and $P=\vec n\cdot\vec\sigma$. Then
--   1. $\langle v|P|v\rangle=\operatorname{Tr}\bigl(\tfrac12(1+\vec v\cdot\vec\sigma)P\bigr)=0$;
--   2. the Bloch vector of $P|v\rangle$ is $-\vec v$: $P\,\tfrac12(1+\vec v\cdot\vec\sigma)\,P=\tfrac12(1-\vec v\cdot\vec\sigma)$.
--
--   Now let $\vec v_k\in S^2$ ($k\in V$) be fixed, choose each $\vec n_k$ independently and uniformly on the equator $\{\vec n\in S^2:\vec n\cdot\vec v_k=0\}$, set $P_k=\vec n_k\cdot\vec\sigma$, and let
--   $$\gamma_{ij}=\pi-\arg\langle v_i|P_j|v_j\rangle\langle v_j|P_i|v_i\rangle .$$
--   3. For $i\ne j$ with $\vec v_i\ne\vec v_j$, $\gamma_{ij}$ is uniformly distributed on an interval of length $2\pi$; with the principal argument in $(-\pi,\pi]$ this interval is $[0,2\pi)$.
--
--   Parts 1 and 2 say each $P_k$ moves $|v_k\rangle$ to the orthogonal state; part 3 is the source of the factor $2/\pi$ in Lemma 12.
--
--   **Formalization Note** The complex number is computed phase-free as $\operatorname{Tr}(\rho_iP_j\rho_jP_i)$. The uniform equator draw is the normalised projection of an independent standard Gaussian vector $g_k\in\mathbb R^3$ (`equator`). The paper writes $\gamma_{ij}\in[-\pi,\pi)$ here and $[0,2\pi)$ on p. 12; with Mathlib's `Complex.arg` the formula takes values in $[0,2\pi)$, which is the interval stated. The hypothesis $\vec v_i\ne\vec v_j$ is added: for $\vec v_i=\vec v_j$ the complex number vanishes and its argument carries no information.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 10, Lemma 11 (and the definition of γ_ij above it)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 10, Lemma 11. Parts 1–2 for a unit Bloch vector `v⃗` and a
unit `n⃗ ⊥ v⃗`, `P = n⃗ · σ⃗`: `⟨v|P|v⟩ = Tr(ρ_v P) = 0` and `P|v⟩⟨v|P = ρ_{−v⃗}`. Part 3: with the
equator draws of Algorithm 17, `γ_ij = π − arg⟨v_i|P_j|v_j⟩⟨v_j|P_i|v_i⟩` is uniformly distributed
(on `[0, 2π)` with Mathlib's `arg ∈ (−π, π]`), for `i ≠ j` and `v⃗_i ≠ v⃗_j`. -/
theorem lemma_11 :
    (∀ (u m : Fin 3 → ℝ), u ⬝ᵥ u = 1 → m ⬝ᵥ m = 1 → m ⬝ᵥ u = 0 →
      (rho1 u * pauliVec m).trace = 0 ∧
      pauliVec m * rho1 u * pauliVec m = rho1 (-u)) ∧
    (∀ {n : ℕ} (v : Fin n → Fin 3 → ℝ), (∀ k, v k ⬝ᵥ v k = 1) →
      ∀ i j : Fin n, i ≠ j → v i ≠ v j →
        Measure.map (fun g => Real.pi - Complex.arg (zval v (equator v g) i j)) (gaussG n) =
          ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ico 0 (2 * Real.pi))) := by sorry

end QMCTriFree.Circuit
