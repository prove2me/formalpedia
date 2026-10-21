-- Prove2me | Theorems.Thm_PostQual_Incumbent_well_defined
-- name    : PostQual.Incumbent.well_defined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:22.685315+00:00
-- url     : https://prove2.me/theorems/4d8f4cae-928b-4969-92f3-1452efbf32a4
-- title:
--   Proof of Theorem 2 (i), pp. ec5–ec6 (PDF 39–40) — if m > m⋆(x0), H(b′) < L^m(b′;x0) for some b′, and D^m_0(p′;x0,R̄+∆) > 0 for some p′
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Let $x_0\in[\underline R,\overline R]$ and $1\le m\le N$ with $m>m^\star(x_0)$. Then
--
--   1. there is $b'\in(\ell(x_0),\overline R+\Delta)$ with $H(b')<L^m(b';x_0)$;
--   2. there is $p'\ge\overline R+\Delta$ with
--   $$D^m_0(p';x_0,\overline R+\Delta)=\Pi^m_0(p';x_0,\overline R+\Delta)-\Pi^m_0(b^\star_m(x_0);x_0,\overline R+\Delta)>0.$$
--
--   The first point makes the set defining $b^\star_m(x_0)$ nonempty when $x_0>\underline R+\Delta$; the second makes the set defining $p^\star_m(x_0)$ nonempty.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), pp. ec5–ec6 (PDF 39–40), proof of Theorem 2 (i), well-definedness of b⋆_m(x0) and p⋆_m(x0)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Proof of Theorem 2 (i), pp. ec5–ec6: if `m > m⋆(x0)` there is `b′ ∈ (max{x0, R̲+∆}, R̄+∆)` with
`H(b′) < L^m(b′; x0)`, and there is `p′ ≥ R̄ + ∆` with `D^m_0(p′; x0, R̄+∆) > 0`. -/
theorem well_defined (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (hm : P.mStar x0 < m) :
    (∃ b' ∈ Set.Ioo (P.lo x0) (P.Rhi + P.Δ), P.H b' < P.L m b' x0) ∧
    (∃ p' ≥ P.Rhi + P.Δ,
      0 < P.Pi m p' x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)) := by sorry

end PostQual.Incumbent
