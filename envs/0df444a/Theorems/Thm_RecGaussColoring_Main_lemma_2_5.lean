-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_2_5
-- name    : RecGaussColoring.Main.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:28.402619+00:00
-- url     : https://prove2.me/theorems/badc807a-89cc-4511-a98a-db4177491380
-- title:
--   Lemma 2.5 — cover composition
-- statement:
--   Fix $c>0$ and sequences $t_k\to\infty$, dimensions $d_k$, finite families $X_k\subset\mathbb R^{d_k}$, and families $Y_{k,x}\subset x^\perp$. Let $\lambda_k,E_k,U_k$ be uniformly bounded with $0\le\lambda_k\le\sqrt{E_k}$ and $U_k^2\ge1/(1+c)$. Suppose eventually $X_k$ is a $(\lambda_kt_k-o(t_k),e^{-o(t_k^2)})$-cover, $\|x\|\le1$, and $\log|X_k|\le E_kt_k^2/2+o(t_k^2)$. Suppose each $Y_{k,x}$ is a $(\sqrt3t_k-o(t_k),e^{-o(t_k^2)})$-cover with norms at most $U_k+o(1)$ and log cardinality at most $3(1+c)t_k^2/2+o(t_k^2)$, with the same error sequences for every $x\in X_k$. Then there exist three error sequences $e_1,e_2=o(t)$ and $f=o(t^2)$ such that eventually
--   $$
--   \Pr\left[\exists x\in X_k,\ y\in Y_{k,x}:\
--   \langle\gamma,x\rangle\ge\lambda_kt_k-e_{1,k},\quad
--   \langle\gamma,y\rangle\ge\left(\sqrt3-\sqrt{(E_k-\lambda_k^2)(U_k^2-1/(1+c))}\right)t_k-e_{2,k}\right]\ge e^{-f_k}.
--   $$
--   This is the strengthened cover-composition result. Its constants and dimension are unrestricted except for the displayed hypotheses.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - reading: as t tends to infinity, with uniform little-o errors → sequences of instances and explicit errors with ratio tending to zero; hypotheses and conclusions eventually; reason: this gives the asymptotic assertions content and permits deletion of finitely many indices
--   - encoding: √E and finite logarithmic cardinalities → E_k≥0 explicitly; cardinalities cast to ℝ before log; reason: the real square root requires a nonnegative argument, and the positive cover probabilities imply nonempty families eventually
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 2.5, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Certificates

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 2.5, pp. 8–9, with all errors uniform over each inner family. -/
theorem lemma_2_5 (c : ℝ) (hc : 0 < c) (d : ℕ → ℕ)
    (t lam E U : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hb : ∃ B : ℝ, ∀ k, |lam k| ≤ B ∧ |E k| ≤ B ∧ |U k| ≤ B)
    (X : (k : ℕ) → Finset (Space (d k)))
    (Y : (k : ℕ) → Space (d k) → Finset (Space (d k)))
    (eX fX lX eY fY nY lY : ℕ → ℝ)
    (heX : SmallO eX t) (hfX : SmallOSq fX t) (hlX : SmallOSq lX t)
    (heY : SmallO eY t) (hfY : SmallOSq fY t)
    (hnY : Vanishes nY) (hlY : SmallOSq lY t)
    (hdata : ∀ᶠ k in atTop,
      0 ≤ E k ∧ 0 ≤ lam k ∧ lam k ≤ Real.sqrt (E k) ∧
      1/(1+c) ≤ (U k)^2 ∧
      IsCover (X k) (lam k*t k-eX k) (Real.exp (-fX k)) ∧
      (∀ x ∈ X k, ‖x‖ ≤ 1) ∧
      Real.log ((X k).card : ℝ) ≤ E k/2*(t k)^2+lX k ∧
      ∀ x ∈ X k,
        (∀ y ∈ Y k x, ⟪y,x⟫ = 0) ∧
        IsCover (Y k x) (Real.sqrt 3*t k-eY k) (Real.exp (-fY k)) ∧
        (∀ y ∈ Y k x, ‖y‖ ≤ U k+nY k) ∧
        Real.log ((Y k x).card : ℝ) ≤ 3*(1+c)/2*(t k)^2+lY k) :
  ∃ e₁ e₂ f : ℕ → ℝ, SmallO e₁ t ∧ SmallO e₂ t ∧ SmallOSq f t ∧
    ∀ᶠ k in atTop, Real.exp (-f k) ≤ gaussProb
      {g | ∃ x ∈ X k, ∃ y ∈ Y k x,
        lam k*t k-e₁ k ≤ ⟪g,x⟫ ∧
        (Real.sqrt 3-Real.sqrt ((E k-(lam k)^2)*((U k)^2-1/(1+c))))*t k-e₂ k ≤ ⟪g,y⟫} := by sorry

end RecGaussColoring.Main
