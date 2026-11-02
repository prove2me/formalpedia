-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_hrw_cmi_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.hrw_cmi_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:14:37.798107+00:00
-- url     : https://prove2.me/theorems/b55c08b1-341d-4768-a6ee-38a43a52039d
-- title:
--   Unnumbered numerical identity: HRW squashed CMI equals nonlocality cost
-- statement:
--   Let $x,y,a,b\in\{0,1\}$. For real parameters $\delta,\eta$, define the binary HRW device as follows. At $x=y=0$, each equal-output event has probability $(1-\delta)/2$ and each unequal-output event has probability $\delta/2$. At every other setting, each CHSH-winning event $a\oplus b=xy$ has probability $3/8-\eta/2$ and each losing event has probability $1/8+\eta/2$. Let $\epsilon(P)$ be the CHSH loss averaged over independent uniform inputs. In the printed single-vertex convention, $C(P)$ is the infimum of $t\in[0,1]$ in decompositions $P=tV+(1-t)L$ with $V$ a nonlocal extreme non-signaling device and $L$ local.
--
--   Assume $0\le\delta\le1$ and $-1/4\le\eta\le1/12-\delta/3$. Compute squashed CMI from the vertex-labelled complete extension, with a general Eve input randomizer after the honest input choice. Define the source cost $N_C(P)=C(P)\log_2\min\{d_A,d_B\}$ using maximum marginal support sizes. Then
--
--   $$\widehat I(A:B\mid E)_{\mathcal E(P)}=N_C(P)=\frac14-\delta-3\eta.$$
--
--   The binary HRW marginals have support two. Optimality against every general CE measurement is asserted as conclusion, never as a hypothesis.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 58, HRW squashed-CMI identity / equations (323), (324)

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

/-- PDF pp.56,58: the source's HRW squashed-CMI/cost identity on its binary
CHSH sector. The equality against ALL general CE measurements is the conclusion;
the displayed witness ensemble is never assumed optimal. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem hrw_cmi_cost (delta eta : ℝ) (hd : 0 ≤ delta) (hdOne : delta ≤ 1)
    (he : -(1/4 : ℝ) ≤ eta) (heUpper : eta ≤ 1/12 - delta/3)
    (c : CompleteExtension (hrwBox delta eta)) :
    squashedCMI c = nonlocalityCost (hrwBox delta eta) false false ∧
    nonlocalityCost (hrwBox delta eta) false false = 1/4 - delta - 3*eta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
