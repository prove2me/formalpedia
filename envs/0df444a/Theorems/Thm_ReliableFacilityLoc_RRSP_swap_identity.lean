-- Prove2me | Theorems.Thm_ReliableFacilityLoc_RRSP_swap_identity
-- name    : ReliableFacilityLoc.RRSP.swap_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:05.621701+00:00
-- url     : https://prove2.me/theorems/193d418b-1d24-4bbb-9fdf-81f57b1ea15d
-- title:
--   Swap identity: exchanging two probability facilities changes $G$ by $\frac{q_j-q_k}{1-q_j}\lambda_i P_{jr}(d_{iu}-d_{iv})$
-- statement:
--   Let $0 \le q_j < 1$ for every regular facility. Let $(Y, Z, P, W)$ be feasible for the split formulation of (RSP$_i$), and let $r$ be a level with $r + 1 \le R - 1$ such that $Z$ puts the regular facility $j$ at level $r$ and the regular facility $k$ at level $r+1$, while $Y$ puts facility $u$ at level $r$ and facility $v$ at level $r + 1$. Let $Z'$ be obtained from $Z$ by exchanging $j$ and $k$ between the levels $r$ and $r+1$, keep $Y$, and let $(Y, Z', P', W')$ be feasible, so that $P'$ and $W'$ are the probabilities computed from $Z'$. Then
--
--   $$
--   G(Y, Z', P') - G(Y, Z, P) = \frac{q_j - q_k}{1 - q_j}\, \lambda_i\, P_{jr}\, (d_{iu} - d_{iv}).
--   $$
--
--   In the proof of Lemma 1 this identity shows that, when $q_j > q_k$ and $d_{iu} \le d_{iv}$, moving the more reliable facility $k$ one level up does not increase the cost. The levels after $r + 1$ are unaffected, because the probability that both levels $r$ and $r+1$ fail is $\frac{q_j q_k}{1-q_j}P_{jr}$ in either order.
--
--   **Formalization Note** $Z'_{\ell s} = Z_{\tau(\ell), s}$ at the levels $s \in \{r, r+1\}$, with $\tau$ the transposition of $j$ and $k$, and $Z'_{\ell s} = Z_{\ell s}$ elsewhere; this is the paper's $Z'$. The paper writes $P'$ explicitly; here $P'$, $W'$ are any arrays making $(Y, Z', P', W')$ feasible, which (19f)–(19k) determine uniquely. The identity is stated without a sign condition on $q_j - q_k$ or $d_{iu} - d_{iv}$. The cost $G$ is the one of the split-formulation definition.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 39 (PDF 41), Appendix A.4, proof of Lemma 1 (unnumbered display); Z′, P′ on p. 38 (PDF 40)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_Split

open Finset

namespace ReliableFacilityLoc.RRSP

/-- **The swap identity in the proof of Lemma 1** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010),
Appendix A.4, p. 39, PDF 41; unnumbered). Let `(Y, Z, P, W)` be feasible for the split formulation,
with regular facilities `j`, `k` at the `Z`-levels `r` and `r + 1` (`r + 1 ≤ R − 1`), and let `u`,
`v` be the `Y`-facilities at the levels `r` and `r + 1`. Let `Z'` exchange `j` and `k` between the
levels `r` and `r + 1` and leave everything else unchanged, and let `(Y, Z', P', W')` be feasible
(so `P'`, `W'` are the probabilities computed from `Z'`). Then
`G(Y, Z', P') − G(Y, Z, P) = (q_j − q_k)/(1 − q_j) · λ_i P_jr (d_iu − d_iv)`.

Printed: "G(Y′,Z′,P′) − G(Y,Z,P) = λi(P′krdiu + P′j,r+1div − Pjrdiu − Pk,r+1div)
= λi[diu(P′kr − Pjr) + div(P′j,r+1 − Pk,r+1)]
= λi{diu[(1 − qk)/(1 − qj) Pjr − Pjr] − div(qkPjr − qj(1 − qk)/(1 − qj) Pjr)}
= (qj − qk)/(1 − qj) λiPjr(diu − div)."

Formalization Note: `Z'` is given by `Z' ℓ s = Z (swap j k ℓ) s` at the levels `s ∈ {r, r + 1}` and
`Z' ℓ s = Z ℓ s` elsewhere, which is the printed `Z'` ("1 if ℓ = k, s = r or ℓ = j, s = r + 1;
0 if ℓ = j, s = r or ℓ = k, s = r + 1; Z_ℓs otherwise", with the stray "h = i" dropped). `P'`, `W'`
are not written out: (19f)–(19k) determine them from `Z'`, and the printed `P'` is what they give.
The identity holds whatever the signs of `q_j − q_k` and `d_iu − d_iv`; the proof of Lemma 1 then
uses `d_iu ≤ d_iv`. `0 ≤ q_j < 1` is the standing assumption of §3.1 (p. 8). -/
theorem swap_identity {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (Y Z P W Z' P' W' : Fin (J + 1) → Fin (R + 1) → ℝ) (j k : Fin J) (u v : Fin (J + 1))
    (r : Fin R) (hr : (r : ℕ) + 1 < R) (hfeas : IsSplitFeasible q Y Z P W)
    (hZj : Z j.castSucc r.castSucc = 1) (hZk : Z k.castSucc r.succ = 1)
    (hYu : Y u r.castSucc = 1) (hYv : Y v r.succ = 1)
    (hZ' : ∀ ℓ s, Z' ℓ s =
      if s = r.castSucc ∨ s = r.succ then Z (Equiv.swap j.castSucc k.castSucc ℓ) s else Z ℓ s)
    (hfeas' : IsSplitFeasible q Y Z' P' W') :
    splitObjective lam d phi mu Y W' - splitObjective lam d phi mu Y W =
      (q j - q k) / (1 - q j) * lam * P j.castSucc r.castSucc * (ReliableFacilityLoc.Supermod.dExt d phi u - ReliableFacilityLoc.Supermod.dExt d phi v) := by sorry

end ReliableFacilityLoc.RRSP
