-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_relativeEntropyIdentities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.relativeEntropyIdentities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:59:06.985745+00:00
-- url     : https://prove2.me/theorems/1b889eb8-456b-4b18-9929-50bbf722ee6a
-- title:
--   Finite-energy relative-entropy identities
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $\rho=|u\rangle\langle u|$ with $\|u\|=1$ have finite photon mean $E$. For $(\mathcal C,\zeta,M)=(\mathcal N_n,1,n)$ with $n>0$, or $(\mathcal E_\eta^N,\eta,(1-\eta)N)$ with $M>0$, put $\rho'=\mathcal C(\rho)$ and let $\tau_M$ be its vacuum-output thermal reference. Then the output energy, output entropy, and the two trace terms defining $D(\rho'\Vert\tau_M)=\operatorname{Tr}\rho'\ln\rho'-\operatorname{Tr}\rho'\ln\tau_M$ are finite, and
--   $$S(\rho')=g(M)+\zeta E\ln\frac{M+1}M-D(\rho'\Vert\tau_M),$$
--   $$S(\rho')\ge g(M)\quad\Longleftrightarrow\quad D(\rho'\Vert\tau_M)\le\zeta E\ln\frac{M+1}M.$$
--   Each spectral and diagonal trace series genuinely converges.
--
--   The equivalence is pointwise on this finite domain; it does not identify a finite-energy assertion with the unrestricted conjecture.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 9, §V.B, Eqs.(61)–(62), (67): entropy and relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.9, Eqs.(61)–(62),(67): identities and pointwise equivalences for
normalized finite-energy pure inputs and faithful positive-temperature reference.
No infinity-minus-infinity or unrestricted finite-energy approximation is used. -/
theorem relativeEntropyIdentities (eta N n : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (u : B.Fock) (hu : ‖u‖ = 1)
    (hE : FiniteEnergy (pureState u)) :
    (0 < n → FiniteRelativeIdentity (displacementNoiseChannel n) 1 n (pureState u)) ∧
    (0 < (1 - eta) * N →
      FiniteRelativeIdentity (thermal eta N) eta ((1 - eta) * N) (pureState u)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
