-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_entropyTypicalRank
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.entropyTypicalRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:25:16.598689+00:00
-- url     : https://prove2.me/theorems/88067ef6-40b1-4fb3-9c3d-48b8ed2b0b9f
-- title:
--   Lemma I.12: (1−K_H/delta²)2^(sum H−delta sqrt(n))≤Tr PiH≤2^(sum H+delta sqrt(n)); eta-shadow trace≥(eta−K_H/delta²)2^(sum H−delta sqrt(n)).
-- statement:
--   Let a nonzero finite system have dimension $d$, and choose a fine orthogonal spectral resolution, including zero eigenspaces and a basis inside degeneracies. All states are normalized, $n>0$, and all typicality tolerances are positive. Write $H$ for entropy in bits, $K_V=2\log_2(e)/e$, $K_H(d)=\max\{(\log_2 3)^2,(\log_2 d)^2\}$, and $h=\sum_iH(\rho_i)$. A shadow $B$ is an effect with state mass at least $\eta$. In the variance bounds put $c=K_Vd\alpha\sqrt n$, $t=2N(\rho)e^{-2\mu(\rho)^2\alpha^2}$, where $N$ counts the positive eigenvalues of $\sqrt{\rho(1-\rho)}$ and $\mu$ is their minimum, or zero on empty support. In the constant-typical bound $\eta(u)=-u\log_2u$, including $u=0$. The weak-law factor states may be noncommuting, with target $\widetilde\rho$ and operator-norm tolerance $\epsilon>0$.
--
--   $$
--   (1-K_H/\delta^2)2^{h-\delta\sqrt n}\le\operatorname{Tr}\Pi_H\le2^{h+\delta\sqrt n},\qquad\operatorname{Tr}B\ge(\eta-K_H/\delta^2)2^{h-\delta\sqrt n}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 14, Lemma I.12

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma I.12, PDF p.14: both rank estimates and the shadow lower bound,
using the same advertised dimension-only K_H as Lemma I.11. -/
theorem entropyTypicalRank {d n : ℕ} (S : Fin n → FineResolution d) (hn : 0 < n)
    (delta : ℝ) (hdelta : 0 < delta) :
    let h := ∑ i, vnEntropy (S i).state
    let e := delta * Real.sqrt n
    (1 - entropyConstant d / delta^2) * exp2 (h - e) ≤ (entropyProjector S delta).trace.re ∧
    (entropyProjector S delta).trace.re ≤ exp2 (h + e) ∧
    ∀ (B : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (eta : ℝ),
      IsShadow (wordTensor (fun i => (S i).state)) B eta →
        B.trace.re ≥ (eta - entropyConstant d / delta^2) * exp2 (h - e) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
