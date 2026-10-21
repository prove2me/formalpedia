-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_crossModelEntropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.crossModelEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:50:59.469844+00:00
-- url     : https://prove2.me/theorems/5c78d945-ebc3-46e9-bdf6-e2148b847626
-- title:
--   Comparison and equivalence of entropy conjectures
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For admissible thermal parameters and $0<t<1$ with $t\le n$,
--   $$m(\mathcal E_\eta^N)\ge m(\mathcal N_{(1-\eta)N}),\qquad m(\mathcal N_n)\ge m(\mathcal E_{1-t}^{(n-t)/t}).$$
--   Consequently the family of classical minimum-entropy conjectures for all $n\ge0$ is equivalent to the family of thermal minimum-entropy conjectures for all admissible $\eta,N$. Here each conjecture is precisely the universal lower bound by its coherent-output entropy. For either model, its coherent-output majorization conjecture implies its entropy conjecture.
--
--   These are conditional implications and comparisons; neither unrestricted conjecture is asserted.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 5, Eqs.(26)–(27): comparison and equivalence of entropy conjectures

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.3–5, Eqs.(13),(26)–(27): model comparisons and equivalence of the global
conjecture families. The finite reverse decomposition uses 0<t<1 and t<=n. -/
theorem crossModelEntropy :
    (∀ eta N : ℝ, 0 ≤ eta → eta ≤ 1 → 0 ≤ N →
      minimumEntropy (displacementNoiseChannel ((1 - eta) * N)) ≤ minimumEntropy (thermal eta N)) ∧
    (∀ n t : ℝ, 0 < t → t < 1 → t ≤ n →
      minimumEntropy (thermal (1 - t) ((n - t) / t)) ≤ minimumEntropy (displacementNoiseChannel n)) ∧
    (∀ n : ℝ, 0 ≤ n → ClassicalMajorizationConjecture n → ClassicalEntropyConjecture n) ∧
    (∀ eta N : ℝ, 0 ≤ eta → eta ≤ 1 → 0 ≤ N →
      ThermalMajorizationConjecture eta N → ThermalEntropyConjecture eta N) ∧
    ((∀ n : ℝ, 0 ≤ n → ClassicalEntropyConjecture n) ↔
      (∀ eta N : ℝ, 0 ≤ eta → eta ≤ 1 → 0 ≤ N → ThermalEntropyConjecture eta N)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
