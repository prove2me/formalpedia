-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_fullWeakDegradabilityClassification
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.fullWeakDegradabilityClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:00:37.706869+00:00
-- url     : https://prove2.me/theorems/17d18a13-6ded-4dcc-ad64-4d1d19b9aaa7
-- title:
--   Full weak-degradability classification outside B2
-- statement:
--   Work on the complete one-mode Fock space, with $[Q,P]=i$, and let $\Phi$ be a trace-class CPTP Gaussian channel. Its real data $(K,\alpha,m)$ act on every input density through $\chi_{\Phi(\rho)}(z)=\chi_\rho(Kz)\exp(-z^T\alpha z/2+im^Tz)$, where $z\in\mathbb R^2$, $\alpha$ is symmetric positive semidefinite, and $\det\alpha\ge((\det K-1)/2)^2$. A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. Exclude precisely class $B_2$ using the determinant and rank invariants of Table 1. There exists a single-mode physical representation of $\Phi$ with a finite thermal environment such that
--
--   $$\det K\le\tfrac12\Longrightarrow E\text{ is anti-degradable relative to }F,\qquad \det K\ge\tfrac12\Longrightarrow E\text{ is weakly degradable relative to }F.$$
--
--   Both conclusions hold at equality. Each recovery is a CPTP channel working for every density input. This supplies the announced classification, without assigning a negative property to the exceptional class.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 15, Abstract; §3.2; Fig.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Abstract and Section 3.2, PDF pp.1,15-17: non-B2 classification.
Both implications include det(K)=1/2. No negative claim about B2 is made. -/
theorem fullWeakDegradabilityClassification (E : FockMap) (g : GaussianData)
    (hE : IsGaussianChannel E g) (hexception : classOf g ≠ .B2) :
    ∃ (U : JointUnitary) (sigma : State ℕ) (N : ℝ),
      IsThermal sigma.coefficients N ∧
      (∀ rho : State ℕ, dilationReceiver U sigma.coefficients rho.coefficients = E rho.coefficients) ∧
      (g.K.det ≤ 1 / 2 →
        AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) ∧
      (1 / 2 ≤ g.K.det →
        WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
