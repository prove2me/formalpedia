-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_cosetEntropy_rate
-- name    : QAlgorithms.Papers.Independent.Support50.P40.cosetEntropy_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:04:44.886988+00:00
-- url     : https://prove2.me/theorems/f84e92cf-1cd0-4928-841e-56459ead1ce5
-- title:
--   Attainable fixed-inner coset-entropy concatenation rate
-- statement:
--   Fix a normalized additive $[p,1,d]$ inner code, $p\ge1$, and complete syndrome and logical-Pauli coset representatives. Its phase-inclusive commuting stabilizer excludes $-I$ and has $p-1$ independent generators. For independent depolarization with $f\in[0,1]$, define $a_i=P_f(e_i\bar S^\perp)$ and $b_{ij}=P_f(e_i s_j\bar S)$, where $j$ ranges over the four logical Paulis and $i$ over $2^{p-1}$ syndromes. Write $H$ for finite entropy in bits, with $0\log_2 0=0$, and set $S_{X2}=\sum_{i:a_i>0}a_iH((b_{ij}/a_i)_j)$.
--
--   The signed yield satisfies
--
--   $$
--   q_C(f)=\frac{1+H((a_i)_i)-H((b_{ij})_{i,j})}{p}
--   =\frac{1-S_{X2}}p.
--   $$
--
--   If $q_C(f)>0$, it is attainable by keeping this inner code fixed and increasing the additive outer block size. Precisely, for every $\epsilon,\delta>0$, all sufficiently large outer sizes $n$ admit $k$ logical qubits, an additive outer isometric encoder, and a local CPTP decoder such that $k\ge(q_C(f)-\delta)pn$. One choice of encoder and decoder works for every normalized unknown input with fidelity at least $1-\epsilon$, and has entanglement fidelity at least $1-\epsilon$. The scheme uses $pn$ physical noisy channel calls and no preshared entanglement or side communication.
--
--   Attainability is attributed by the paper to Shor–Smolin [14]; the compact coset formula is the present paper's derivation. Negative signed yields are not negative capacities.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 11, Section III, Eqs. (13)-(20): attainable coset-entropy concatenation rate

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.11--13, Eqs.(13)--(20), Fig.4 p.28. Attainability of the
concatenation scheme is attributed on p.11 to Shor--Smolin [14],
quant-ph/9604006; this paper derives its coset-entropy expression. The
positive signed yield is attained by this fixed-inner scheme, not merely
bounded by an unrelated capacity parameter. -/
theorem cosetEntropy_rate {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    signedYield C T f = (1 - conditionalBellEntropy C T f) / (m + 1) ∧
    (0 < signedYield C T f → FixedInnerAchievable C f (signedYield C T f)) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
