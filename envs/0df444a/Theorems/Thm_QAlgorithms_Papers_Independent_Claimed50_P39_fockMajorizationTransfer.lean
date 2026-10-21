-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_fockMajorizationTransfer
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.fockMajorizationTransfer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:01:04.88709+00:00
-- url     : https://prove2.me/theorems/a17821e2-1829-47d8-b854-f1b9fb40b84c
-- title:
--   Conditional transfer of Fock majorization
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Fix admissible $\eta,N$ and suppose that for every $m\in\mathbb N$, the classical vacuum output at noise $M=(1-\eta)N$ majorizes the classical output of $|m\rangle$. Then, for every $k\in\mathbb N$,
--   $$\mathcal E_\eta^N(|0\rangle\langle0|)\succ\mathcal E_\eta^N(|k\rangle\langle k|).$$
--   Here $X\succ Y$ means that both are densities and every decreasing-eigenvalue partial sum of $X$ is at least the corresponding sum of $Y$.
--
--   The classical all-Fock premise is retained exactly; it is not inferred from the one-photon special case.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 10, §VI.A, Eq.(76): conditional transfer of Fock majorization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Eq.(76): conditional transfer to thermal Fock outputs. The
classical premise is retained; no all-Fock majorization conjecture is proved. -/
theorem fockMajorizationTransfer (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N)
    (hclassical : ∀ m : ℕ, Majorizes (displacementNoiseChannel ((1 - eta) * N) (B.fockDyad 0 0))
      (displacementNoiseChannel ((1 - eta) * N) (B.fockDyad m m))) :
    ∀ k : ℕ, Majorizes (thermal eta N (B.fockDyad 0 0)) (thermal eta N (B.fockDyad k k)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
