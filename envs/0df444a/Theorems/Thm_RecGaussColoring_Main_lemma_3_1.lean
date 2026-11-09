-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_3_1
-- name    : RecGaussColoring.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:20.825996+00:00
-- url     : https://prove2.me/theorems/d034d8c2-3268-44a0-a9f3-08a62750c3da
-- title:
--   Lemma 3.1 — correlation bound and potential increase
-- statement:
--   Fix $0<c<c^\dagger$, $(a,\lambda)\in K=[-L,L]\times[0,\sqrt{5+3c}]$, $|y|\le\sqrt{c/(1+c)}$, and a real $\tau\le\mu(c)/2$. With $a_{\rm new}=B(a,y)$ and $\lambda_{\rm new}$ exactly the transition of Lemma 2.8, both conclusions hold:
--   $$
--   |a_{\rm new}|\le L,\qquad
--   V(a_{\rm new},\lambda_{\rm new})-V(a,\lambda)\ge\mu(c)-\tau.
--   $$
--   This is the numerical assertion governing every feasible transition, retaining both parts of the source lemma.
--
--   Differences from the source:
--   - encoding: parameters of certificates related by Lemma 2.8 → the corresponding real numbers and the explicit transition formula; reason: the proof uses only their numerical bounds, so every certificate transition specializes to this assertion
--   - generalization: positive loss τ from Lemma 2.8, also τ≤µ(c)/2 → every real τ≤µ(c)/2; reason: τ is subtracted linearly in both the transition and the lower bound; the two conclusions hold without the other loss restrictions
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 3.1, p. 18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Parameters

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 3.1, p. 18: the two numerical conclusions together. -/
theorem lemma_3_1 (c : ℝ) (hc : 0 < c) (hcD : c < cDagger)
    (a lam y τ : ℝ) (hK : (a,lam) ∈ parameterRegion c)
    (hy : y ∈ Set.Icc (-typeBound c) (typeBound c)) (hτ : τ ≤ mu c/2) :
  |transB a y| ≤ corrBound c ∧
    mu c-τ ≤ potential c (transB a y) (nextLambda c a lam y τ) - potential c a lam := by sorry

end RecGaussColoring.Main
