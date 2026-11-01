-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_loose_parity_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.loose_parity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:03:07.018237+00:00
-- url     : https://prove2.me/theorems/6278db77-ac0d-4047-ad5f-c2a4eed53dbd
-- title:
--   Loose ECC-conditioned parity bound
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   For an information input $i$, put $\phi_i=\sum_j E_{i,j}\otimes|i\oplus j\rangle$, $\eta_l=2^{-n}\sum_i(-1)^{l\cdot i}\phi_i$, and $d_l^2=\|\eta_l\|^2$. Dot products are modulo two and inner products conjugate the first argument.
--
--   Let $C\subseteq\mathbb F_2^n$ be the binary linear code and let $S=C^\perp$ be the span of all disclosed parity rows. Equivalently the parity check matrix is a basis of $S$, so is full rank. Fix an announced syndrome coset $i_0+C$ and use its uniform distribution, independently of the fixed public code choice. Let $v\notin S$ be the PA mask, put $\widehat v=\min_{w\in S}|v\oplus w|$, and let $SD_v$ be the supremum, over all finite POVMs, of mutual information in bits on the purified states $|\phi_i\rangle\langle\phi_i|$ about $v\cdot i$. Thus both parity classes are nonempty and equally likely. Disclosed other PA bits, when present, are included in $S$.
--
--   Put $r=\dim C^\perp$. For every real $\alpha>0$,
--
--   $$SD_v\le2^r\left(\alpha+\frac1\alpha\sum_{2|l|\ge\widehat v}d_l^2\right).$$
--
--   If $m-1$ other independent PA parities are also disclosed, include their rows in the disclosed span: its dimension is then $r+m-1$, giving the factor $2^{r+m-1}$ of Eq. (25). This is the source's ECC-conditioned version of the earlier BBBGM bound [3].
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 19, Appendix G.1 unnumbered lemma, Eqs.(23)–(25): loose parity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix G.1, PDF pp.19--20, Eqs.(23)--(25): loose parity bound. The
ensemble retains the error-labelled purification. The factor 2^r uses
r=dim(C-perp); adding m-1 independent PA disclosures to this
span gives exactly Eq.(25)'s factor 2^(r+m-1). Provenance: BBBGM [3]. -/
theorem loose_parity_bound {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (i0 v : Fin n → ZMod 2)
    (hv : v ∉ binDual C) (alpha : ℝ) (ha : 0 < alpha) :
    parityInformation (conditionedSymmetric U e0 iT jT) C i0 v ≤
      (2 : ℝ) ^ Module.finrank (ZMod 2) (binDual C) *
        (alpha + fourierTail (conditionedSymmetric U e0 iT jT)
          (distanceToSpan (binDual C) v) / alpha) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
