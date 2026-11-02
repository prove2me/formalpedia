-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_hrw_loss_fraction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.hrw_loss_fraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:15:37.200956+00:00
-- url     : https://prove2.me/theorems/08051ab7-0887-4eea-a1cf-55a8a0316dad
-- title:
--   Unnumbered HRW formula (320) and local fraction
-- statement:
--   Let $x,y,a,b\in\{0,1\}$. For real parameters $\delta,\eta$, define the binary HRW device as follows. At $x=y=0$, each equal-output event has probability $(1-\delta)/2$ and each unequal-output event has probability $\delta/2$. At every other setting, each CHSH-winning event $a\oplus b=xy$ has probability $3/8-\eta/2$ and each losing event has probability $1/8+\eta/2$. Let $\epsilon(P)$ be the CHSH loss averaged over independent uniform inputs. In the printed single-vertex convention, $C(P)$ is the infimum of $t\in[0,1]$ in decompositions $P=tV+(1-t)L$ with $V$ a nonlocal extreme non-signaling device and $L$ local.
--
--   For $0\le\delta\le1$ and $-1/4\le\eta\le3/4$, the HRW device is valid and non-signaling, and
--
--   $$\epsilon(P)=\frac14\left(\frac34+\delta+3\eta\right).$$
--
--   Within the further sector $\eta\le1/12-\delta/3$,
--
--   $$C(P)=\frac14-\delta-3\eta,\qquad P\text{ is nonlocal}\ \Longleftrightarrow\ \epsilon(P)<\frac14.$$
--
--   The feasible sector prevents empty-set infimum defaults; this statement makes no fraction claim for other CHSH sectors.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 56, Equations (319), (320) and following local-fraction formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

/-- PDF p.56, (319),(320): validity on the full printed rectangle and the loss
formula. The fraction and local/nonlocal boundary refer only to the indicated
CHSH sector, including its local endpoint. No other relabeling sector is claimed. -/
theorem hrw_loss_fraction (delta eta : ℝ)
    (hd : 0 ≤ delta) (hdOne : delta ≤ 1) (he : -(1/4 : ℝ) ≤ eta) (heUpper : eta ≤ 3/4) :
    ValidDevice (hrwBox delta eta) ∧
    chshLoss (hrwBox delta eta) = (1/4 : ℝ) * (3/4 + delta + 3*eta) ∧
    (eta ≤ 1/12 - delta/3 →
      nonlocalityFraction (hrwBox delta eta) = 1/4 - delta - 3*eta ∧
      (¬ HasLocalModel (hrwBox delta eta) ↔ chshLoss (hrwBox delta eta) < 1/4)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
