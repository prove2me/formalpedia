-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_identification_resolvability_relations
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.identification_resolvability_relations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:51:20.293393+00:00
-- url     : https://prove2.me/theorems/b665017a-6419-4fc7-a28f-e617035e852a
-- title:
--   Theorem 4: general identification and resolvability capacity relations
-- statement:
--   Let $\mathbf W=(W^n:X_n\to\mathcal P(Y_n))$ be arbitrary discrete stochastic channels with $|X_n|=d^n$ for a positive integer $d$. No stationarity, memorylessness or strong converse is assumed. All logarithms are natural and resolvability error is full L1. For an input-law sequence $\mathbf p=(p_n)$ and channel sequence $\mathbf W$, put $T_n(a)=\mathbb P_{p_n(x)W_x^n(y)}\{n^{-1}\log[W_x^n(y)/W_{p_n}^n(y)]>a\}$. Define $\underline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\liminf_nT_n(a)\le\epsilon\}$ and $\overline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\limsup_nT_n(a)\le\epsilon\}$. At $\epsilon=1$ use the strict tail bound $<1$. Spectra and numerical extrema are extended-valued.
--
--   Let $D(\mu,\lambda)$ optimize the liminf double-log message rate of nonempty stochastic identification codes, with limsup first error strictly below $\mu$ and limsup second error at most $\lambda$. For $D^\dagger$ change only the first-error limsup to liminf; at $\mu=0$ replace its strict condition by equality to zero. Both capacities have the operational zero-rate baseline. Let $S(\epsilon)$ be the INFIMUM of nonnegative simulation rates for which the worst-input, best-tuple-code error has limsup at most $\epsilon$; $S^\dagger$ uses liminf. At $\epsilon=2$ use strict error $<2$.
--
--   For $0\le\epsilon<1$,
--   $$
--   \sup_{\mathbf p}\underline I(\epsilon)\le D(1-\epsilon,0)\le S^\dagger(\epsilon)\le\sup_{\mathbf p}\underline I(\epsilon/2),
--   $$
--   $$
--   \sup_{\mathbf p}\overline I(\epsilon)\le D^\dagger(1-\epsilon,0)\le S(\epsilon)\le\sup_{\mathbf p}\overline I(\epsilon/2).
--   $$
--   Separately, each first inequality holds for $0\le\epsilon\le1$, and each third inequality holds for $0\le\epsilon\le2$. In particular,
--   $$
--   \sup_{\mathbf p}\underline I(0)=D(1,0)=S^\dagger(0),\qquad
--   \sup_{\mathbf p}\overline I(0)=D^\dagger(1,0)=S(0).
--   $$
--   The argument $\mathbf p,\mathbf W$ is suppressed only in these displays. These equalities identify the two general-channel zero-error resolvability capacities. The printed supremum in the definition of $S$ is corrected to the infimum used by the proof; otherwise the upward-closed feasible rate set gives infinity.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 8, Theorem 4, (24)–(27): general identification/resolvability capacity relations (paper seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF pp.7–9, Theorem 4, (24)–(27): both chains, SEPARATE endpoint
extensions and both zero-error identities. The simulation definition uses the
proof-mandated INF correction to the printed SUP on p.7.
Printed identification-rate suprema have no singleton convention. Changed to
an explicit zero-rate baseline, as required by the constant-channel zero-error
identities; singleton double-log rates themselves remain minus infinity. -/
theorem identification_resolvability_relations {X Y : ℕ → Type*}
    [∀ k, Fintype (X k)] [∀ k, Nonempty (X k)]
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (hW : ∀ k, IsDiscreteStochastic (W k))
    (d : ℕ) (hd : 0 < d) (hcard : ∀ k, Fintype.card (X k) = d ^ length k) :
    (∀ eps : ℝ, 0 ≤ eps → eps < 1 →
      ((⨆ p, epsilonInformationSpectrum false W p eps) ≤ identificationCapacity false W (1 - eps) 0 ∧
       identificationCapacity false W (1 - eps) 0 ≤ simulationCapacity true W eps ∧
       simulationCapacity true W eps ≤ ⨆ p, epsilonInformationSpectrum false W p (eps / 2)) ∧
      ((⨆ p, epsilonInformationSpectrum true W p eps) ≤ identificationCapacity true W (1 - eps) 0 ∧
       identificationCapacity true W (1 - eps) 0 ≤ simulationCapacity false W eps ∧
       simulationCapacity false W eps ≤ ⨆ p, epsilonInformationSpectrum true W p (eps / 2))) ∧
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (⨆ p, epsilonInformationSpectrum false W p eps) ≤ identificationCapacity false W (1 - eps) 0 ∧
      (⨆ p, epsilonInformationSpectrum true W p eps) ≤ identificationCapacity true W (1 - eps) 0) ∧
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 2 →
      simulationCapacity true W eps ≤ (⨆ p, epsilonInformationSpectrum false W p (eps / 2)) ∧
      simulationCapacity false W eps ≤ (⨆ p, epsilonInformationSpectrum true W p (eps / 2))) ∧
    ((⨆ p, epsilonInformationSpectrum false W p 0) = identificationCapacity false W 1 0 ∧
      identificationCapacity false W 1 0 = simulationCapacity true W 0) ∧
    ((⨆ p, epsilonInformationSpectrum true W p 0) = identificationCapacity true W 1 0 ∧
      identificationCapacity true W 1 0 = simulationCapacity false W 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
