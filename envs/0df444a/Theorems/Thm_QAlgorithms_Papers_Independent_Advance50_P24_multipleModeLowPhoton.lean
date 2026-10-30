-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_multipleModeLowPhoton
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.multipleModeLowPhoton
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:02:49.012823+00:00
-- url     : https://prove2.me/theorems/02327cbe-9042-43a8-af7b-bc758f80436f
-- title:
--   General multimode low-photon law, including the zero-capacity branch
-- statement:
--   Fix a finite passive vacuum-loss wiretap channel with $m\ge1$ Alice modes, $k$ Bob modes, $l$ Eve modes and $m\le k+l$, with complex unitary transition matrix $t$ as in (23). All non-Alice input ports are vacuum, and Eve receives every non-Bob output. Let $\eta_{\max}$ be the largest eigenvalue of $t_{ab}^\dagger t_{ab}$, and let $C_P^M(t,N)$ be the operational message-Holevo private capacity in nats under codebook-average total block photon energy at most $nN$. Arbitrary mixed inputs entangled across modes and uses are allowed. The capacity is finite for every $N\ge0$. Define $c_t=\max(0,2\eta_{\max}-1)$ and $r_t(N)=C_P^M(t,N)-c_tN\log(1/N)$. Then
--
--   $$C_P^M(t,N)=c_tN\log(1/N)+r_t(N),\qquad r_t(N)=O(N),\qquad \limsup_{N\downarrow0}\left|r_t(N)/N\right|<\infty.$$
--
--   The limit is through positive budgets and constants may depend on the fixed channel. If $\eta_{\max}\le1/2$, the capacity is exactly zero for every $N\ge0$. The source's signed coefficient is corrected by its positive part; its favorable branch and absolute limsup remain unchanged.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 4, Theorem 5, (43)–(44): multiple-mode low-photon expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 5, PDF p.4, (43)--(44), with the minimal all-domain correction.
Printed: leading coefficient 2*eta_max-1 on the full physical domain.
Changed: its positive part, and explicit zero capacity when eta_max<=1/2.
Why: Theorems 1 and 4 force zero on that branch, whereas a negative leading
coefficient contradicts nonnegative capacity. The positive branch is unchanged.
The whole complex unitary channel is fixed before the positive N limit. The
remainder retains O(N) and finite limsup ABSOLUTE ratio, not a signed limit. -/
theorem multipleModeLowPhoton {m k l : ℕ} (hm : 0 < m) (hdim : m ≤ k + l)
    (t : Matrix.unitaryGroup (Fin (k + l)) ℂ) :
    (∀ N : ℝ, 0 ≤ N → passiveCapacity m k l
      (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) N ≠ ⊤) ∧
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (passiveRemainder m k l hm hdim t) (fun N : ℝ => N) ∧
    Filter.limsup (fun N : ℝ =>
      ((|passiveRemainder m k l hm hdim t N / N| : ℝ) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) < ⊤ ∧
    (largestTransmissivity hm
        (aliceBobBlock hdim (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)) ≤ 1 / 2 →
      ∀ N : ℝ, 0 ≤ N → passiveCapacity m k l
        (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) N = 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
