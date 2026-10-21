-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_corollaryOne_ecdUniform
-- name    : QAlgorithms.Papers.Independent.Next46.P08.corollaryOne_ecdUniform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:54:02.169982+00:00
-- url     : https://prove2.me/theorems/dbdc2f09-965f-4f4a-95fd-5f2c94fda8f6
-- title:
--   Corrected Corollary 1: ECD-uniform continuity of output Holevo information
-- statement:
--   Let $A,B$ be infinite-dimensional separable complex quantum systems with positive densely defined self-adjoint Hamiltonians $H_A,H_B$. Assume $H_A$ has discrete spectrum of finite multiplicity tending to infinity and $\operatorname{Tr}e^{-\beta H_B}<\infty$ for every $\beta>0$. Write $E_0^A,E_0^B$ for their spectral infima. Let $\mu$ be any Borel probability ensemble on the trace-norm state space of $A$, whose barycenter $\bar\rho=\int\rho\,\mu(d\rho)$ has finite input energy. Fix $E>E_0^B$ and $L>E_0^A$. For channels $\Phi,\Psi$, write $D_L(\Phi,\Psi)$ for the supremum of $\|((\Phi-\Psi)\otimes\mathrm{Id}_R)(\omega)\|_1$ over all normalized states $\omega$ on $A\otimes R$ with $\operatorname{Tr}H_A\omega_A\le L$, using a fixed infinite-dimensional separable reference $R$. Write $\chi(\Phi(\mu))$ for the integral of output relative entropy to $\Phi(\bar\rho)$, in nats.
--
--   On the set $\mathcal F_{\mu,E}=\{\Phi:\operatorname{Tr}H_B\Phi(\bar\rho)\le E\}$ this information is finite and uniformly continuous for $D_L$:
--
--   $$
--   \forall\eta>0\ \exists\delta>0\ \forall\Phi,\Psi\in\mathcal F_{\mu,E},\quad
--   D_L(\Phi,\Psi)<\delta\ \Longrightarrow\
--   |\chi(\Phi(\mu))-\chi(\Psi(\mu))|<\eta.
--   $$
--
--   The same $\delta$ works for all channels in the displayed set. This explicitly corrected statement specifies the ECD uniformity; it does not assert uniform continuity for every metric with the same topology.
--
--   **Formalization Note** The Hamiltonian eigenbasis coordinates are exhaustive under these spectral assumptions. The barycenter and its output energy are computed; individual ensemble members have no separate energy bound. Finiteness is included before real conversion.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 12, Corollary 1: explicitly corrected ECD-uniform content

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary 1, PDF p.12: corrected ECD-uniform content. Printed: uniform
continuity for EVERY metric inducing the strong topology (Remark 4).
Changed: every SPECIFIED ECD level L>E0_A. Reason: a topology alone does
not identify uniformities. Both spectral assumptions justify eigenbasis
coordinates. Individual ensemble members need not have bounded energy. -/
theorem corollaryOne_ecdUniform
    (energyA energyB : ℕ → ℝ≥0)
    (hA : QAlgorithms.Papers.Independent.Claimed50.P32.IsEnergyOperator energyA)
    (hB : EigenbasisGibbsCondition energyB) (mu : GeneralizedEnsemble ℕ)
    (hmu : diagonalEnergy energyA (ensembleBarycenter mu) < ⊤)
    (E : ℝ) (hE : eigenbasisGroundEnergy energyB < E)
    (L : ℝ) (hL : eigenbasisGroundEnergy energyA < L) :
    (∀ Phi : StrongChannel ℕ ℕ,
      diagonalEnergy energyB (Phi.val.act (ensembleBarycenter mu)) ≤ ENNReal.ofReal E →
      ensembleHolevo Phi.val.act mu < ⊤) ∧
    (∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ Phi Psi : StrongChannel ℕ ℕ,
        diagonalEnergy energyB (Phi.val.act (ensembleBarycenter mu)) ≤ ENNReal.ofReal E →
        diagonalEnergy energyB (Psi.val.act (ensembleBarycenter mu)) ≤ ENNReal.ofReal E →
        ecdMagnitude energyA L Phi Psi < ENNReal.ofReal delta →
        |(ensembleHolevo Phi.val.act mu).toReal - (ensembleHolevo Psi.val.act mu).toReal| < eta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
