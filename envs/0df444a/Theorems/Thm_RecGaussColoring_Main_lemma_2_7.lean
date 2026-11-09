-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_2_7
-- name    : RecGaussColoring.Main.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:04.997954+00:00
-- url     : https://prove2.me/theorems/5663bd12-2f37-4d07-b9c6-c1c972508094
-- title:
--   Lemma 2.7 — level-two certificate
-- statement:
--   Fix $0<c<c^\dagger$ and $\tau>0$. Along a sequence of three-colorable graphs with $n_k\to\infty$, take strict vector three-colorings, $\Delta(G_k)\le n_k^{3(1+c)/(5+3c)}$, and thresholds satisfying $\Phi^c(t_k)=n_k^{-1/(5+3c)}$. Let $G_k[W_k]$ carry the local covers of Lemma 1.3(ii), and choose roots $i_k\in W_k$. There are intervals $J_k=[l_k,h_k]\subseteq[-1,1]$ eventually of width at most $(\log t_k)^{-2}$, retained sets $\widetilde S_k^{(1)}\subseteq N_{G_k[W_k]}(i_k)$, and numbers $|y_k|\le\sqrt{c/(1+c)}$ such that the constructed sets
--   $$
--   S_k^{(2)}=\{u\in W_k:\exists j\in\widetilde S_k^{(1)},\ ju\in E(G_k),\ \langle u_{i_k\mid j},u_{u\mid j}\rangle\in J_k\}
--   $$
--   are level-two certificates with parameters
--   $$
--   \bigl(b_2(y_k),(\lambda_2(y_k)-\tau)t_k-o(t_k),e^{-o(t_k^2)}\bigr).
--   $$
--   Here $b_2$ and $\lambda_2$ are exactly the arithmetic functions displayed on p. 12. This supplies the first propagated certificate; $y_k$ need not be constant.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - reading: as t tends to infinity, with uniform little-o errors → sequences of instances and explicit errors with ratio tending to zero; hypotheses and conclusions eventually; reason: this gives the asymptotic assertions content and permits deletion of finitely many indices
--   - reading: some y and interval chosen at threshold t → one y_k and, when relevant, interval J_k per instance; reason: the interval midpoint in the proof depends on t; parameters a_k and λ_k may also vary
--   - generalization: condition (i) fails, hence condition (ii) holds → condition (ii) is assumed without failure of (i); reason: the proofs use only the resulting local covers; every source instance is retained
--   - encoding: normalized directions with nonzero denominator → eventually every supported root correlation has absolute value less than one; reason: normalization must be defined; in these lemmas this follows from the uniform correlation approximation and bounds strictly below one
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 2.7, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Certificates

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 2.7, p. 12, with the interval and y chosen per instance. -/
theorem lemma_2_7 (c : ℝ) (hc : 0 < c) (hcD : c < cDagger)
    (D : CertificateData) (t : ℕ → ℝ) (hD : CertificateSetting c D t)
    (τ : ℝ) (hτ : 0 < τ) :
  ∃ lo hi y : ℕ → ℝ,
    ∃ retained : (k : ℕ) → Finset (Fin (D.graph k).n),
      (∀ᶠ k in atTop,
        -1 ≤ lo k ∧ lo k ≤ hi k ∧ hi k ≤ 1 ∧
        hi k-lo k ≤ (Real.log (t k))^(-2 : ℤ) ∧
        (∀ j ∈ retained k, j ∈ D.region k ∧ (D.graph k).G.Adj (D.root k) j)) ∧
      (∀ k, y k ∈ Set.Icc (-typeBound c) (typeBound c)) ∧
      AsymptoticCertificate D t 2
        (fun k => levelTwoSet D k (retained k) (lo k) (hi k))
        (fun k => bTwo (y k)) (fun k => lambdaTwo c (y k)-τ) := by sorry

end RecGaussColoring.Main
