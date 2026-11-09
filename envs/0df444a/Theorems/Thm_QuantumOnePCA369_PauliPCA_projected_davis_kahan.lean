-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_projected_davis_kahan
-- name    : QuantumOnePCA369.PauliPCA.projected_davis_kahan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:55.16326+00:00
-- url     : https://prove2.me/theorems/0434253a-6507-4688-9c97-589c270aa65d
-- title:
--   Lemma 4.1 — projected Davis–Kahan bound
-- statement:
--   Let $\sigma=\lambda|\psi\rangle\langle\psi|+\nu\in\mathbb C^{d\times d}$ with $|\psi\rangle$ a unit vector, $\lambda>0$, $\nu\succeq0$, and
--   $$\langle\psi|\nu|\psi\rangle=0,\qquad\lambda-\|\nu\|_\infty\ge\Delta>0.$$
--   Let $\xi$ be Hermitian, $\Pi$ any orthogonal projection, and $|\hat\psi\rangle$ a top unit eigenvector of $\hat\sigma=\Pi\sigma\Pi+\xi$ (an arbitrary unit vector if $\hat\sigma=0$). There is a universal constant $C$ with
--   $$1-|\langle\hat\psi|\psi\rangle|^2\le C\Big(\frac{\lambda}{\Delta}\|(I-\Pi)|\psi\rangle\|_2^2+\frac{\|\xi\|_\infty^2}{\Delta^2}\Big).$$
--
--   This is the final-layer guarantee: the top eigenvector of a compressed, perturbed estimate is close to the true top eigenvector once the compression loses little of $|\psi\rangle$ and the perturbation is small relative to the gap.
--
--   **Formalization Note** "Top eigenvector" means a unit eigenvector whose real eigenvalue is at least every eigenvalue; when $\hat\sigma=0$ every unit vector qualifies, which is the source's parenthetical case. The matrices are indexed by an arbitrary finite type.
--
--   Differences from the source:
--   - encoding: a top eigenvector of σ̂ (or an arbitrary unit vector if σ̂ = 0) → IsTopEigvec σ̂ ψ̂: unit, σ̂ψ̂ = μψ̂ with μ real and ≥ every eigenvalue; reason: for σ̂ = 0 every unit vector satisfies this, so the parenthetical case is included
--   - encoding: σ ∈ C^{d×d} → matrices indexed by any finite type ι; reason: a relabeling of C^d
--   - encoding: ≲ → one universal constant C quantified before all data; reason: the source's constant is absolute
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 12, Lemma 4.1 (proof pp. 12–13)

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic

open scoped ComplexOrder

namespace QuantumOnePCA369.PauliPCA

theorem projected_davis_kahan :
    ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (ψ ψhat : ι → ℂ) (lam Δ : ℝ)
      (ν ξ Pj : Matrix ι ι ℂ),
      normSq2 ψ = 1 → 0 < lam → ν.PosSemidef → braket ψ (ν.mulVec ψ) = 0 →
      0 < Δ → Δ ≤ lam - opNorm ν → ξ.IsHermitian → IsOrthProj Pj →
      IsTopEigvec (Pj * ((lam : ℂ) • Matrix.vecMulVec ψ (star ψ) + ν) * Pj + ξ) ψhat →
      1 - Complex.normSq (braket ψhat ψ) ≤
        C * (lam / Δ * normSq2 ((1 - Pj).mulVec ψ) + opNorm ξ ^ 2 / Δ ^ 2) := by sorry

end QuantumOnePCA369.PauliPCA
