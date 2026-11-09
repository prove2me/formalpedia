-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_2_8
-- name    : RecGaussColoring.Main.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:26.831206+00:00
-- url     : https://prove2.me/theorems/eec68732-4118-43a7-8154-701ac231560a
-- title:
--   Lemma 2.8 — certificate extension
-- statement:
--   Fix $0<c<c^\dagger$ and $0<\tau<\nu_0(c)/2$. Use the same sequence setting, degree bound, Gaussian thresholds, local covers and roots as Lemma 2.7. Let $\ell\ge1$ be fixed, and suppose $S_k^{(\ell)}$ is a level-$\ell$ certificate with parameters $(a_k,\lambda_kt_k-o(t_k),e^{-o(t_k^2)})$, where $|a_k|\le L$ and $0\le\lambda_k\le\sqrt{5+3c}$. Then some sequence $|y_k|\le\sqrt{c/(1+c)}$ and sets $S_k^{(\ell+1)}$ give level-$(\ell+1)$ certificates with parameters
--   $$
--   \bigl(B(a_k,y_k),\lambda_{{\rm new},k}t_k-o(t_k),e^{-o(t_k^2)}\bigr),
--   $$
--   $$
--   \lambda_{{\rm new},k}=\frac{\lambda_kA(a_k,y_k)+3/2-(\sqrt3/2)\sqrt{(5+3c-\lambda_k^2)(c/(1+c)-y_k^2)}}{\sqrt{1-B(a_k,y_k)^2}}-\tau.
--   $$
--   This is the extension result at every fixed walk level, with no prescribed matching selector or dimension.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - reading: as t tends to infinity, with uniform little-o errors → sequences of instances and explicit errors with ratio tending to zero; hypotheses and conclusions eventually; reason: this gives the asymptotic assertions content and permits deletion of finitely many indices
--   - reading: some y and interval chosen at threshold t → one y_k and, when relevant, interval J_k per instance; reason: the interval midpoint in the proof depends on t; parameters a_k and λ_k may also vary
--   - generalization: condition (i) fails, hence condition (ii) holds → condition (ii) is assumed without failure of (i); reason: the proofs use only the resulting local covers; every source instance is retained
--   - encoding: normalized directions with nonzero denominator → eventually every supported root correlation has absolute value less than one; reason: normalization must be defined; in these lemmas this follows from the uniform correlation approximation and bounds strictly below one
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 2.8; Appendix A, pp. 23–25, p. 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Certificates

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 2.8, p. 16 (Appendix A, pp. 23–25). -/
theorem lemma_2_8 (c : ℝ) (hc : 0 < c) (hcD : c < cDagger)
    (D : CertificateData) (t : ℕ → ℝ) (hD : CertificateSetting c D t)
    (τ : ℝ) (hτ0 : 0 < τ) (hτν : τ < nuZero c/2)
    (l : ℕ) (hl : 1 ≤ l)
    (S : (k : ℕ) → Finset (Fin (D.graph k).n)) (a lam : ℕ → ℝ)
    (ha : ∀ k, |a k| ≤ corrBound c)
    (hlam : ∀ k, 0 ≤ lam k ∧ lam k ≤ Real.sqrt (5+3*c))
    (hcert : AsymptoticCertificate D t l S a lam) :
  ∃ y : ℕ → ℝ, (∀ k, y k ∈ Set.Icc (-typeBound c) (typeBound c)) ∧
    ∃ Snew : (k : ℕ) → Finset (Fin (D.graph k).n),
      AsymptoticCertificate D t (l+1) Snew
        (fun k => transB (a k) (y k))
        (fun k => nextLambda c (a k) (lam k) (y k) τ) := by sorry

end RecGaussColoring.Main
