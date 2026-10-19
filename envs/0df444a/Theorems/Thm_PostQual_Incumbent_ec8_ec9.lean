-- Prove2me | Theorems.Thm_PostQual_Incumbent_ec8_ec9
-- name    : PostQual.Incumbent.ec8_ec9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:26.377915+00:00
-- url     : https://prove2.me/theorems/53a78784-4e3e-4cb0-bf04-c079eea319f0
-- title:
--   (EC.8)–(EC.9), p. ec5 (PDF 39) — ζ^m = (1−β)^m F_e^{m−1} F_e(p−∆)^{−m} f_e (H − L^m) on the support, and ζ^m > 0 beyond it
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Let $x_0\in[\underline R,\overline R]$, $1\le m\le N$ and $p>\ell(x_0)$. With $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $L^m(b;x)=m\beta(b-x)/(1-\beta)$:
--
--   1. for $b\in[\ell(x_0),\overline R+\Delta]$,
--   $$\zeta^m(b;x_0,p)=(1-\beta)^m[F_e(b-\Delta)]^{m-1}[F_e(p-\Delta)]^{-m}f_e(b-\Delta)\big(H(b)-L^m(b;x_0)\big);$$
--   2. for $b>\overline R+\Delta$, $\zeta^m(b;x_0,p)=(1-\beta)^m[F_e(p-\Delta)]^{-m}>0$.
--
--   So on the support the sign of $\zeta^m$ is the sign of $H-L^m$, and beyond it $\zeta^m$ is positive.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec5 (PDF 39), proof of Theorem 2, (EC.8) and (EC.9)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- (EC.8)–(EC.9), p. ec5: `ζ^m(b; x0, p) = (1−β)^m Fe(b−∆)^{m−1} Fe(p−∆)^{−m} fe(b−∆) (H(b) − L^m(b; x0))`
on `[max{x0, R̲+∆}, R̄+∆]`, and `ζ^m(b; x0, p) = (1−β)^m Fe(p−∆)^{−m} > 0` for `b > R̄ + ∆`. -/
theorem ec8_ec9 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (p : ℝ) (hp : P.lo x0 < p) :
    (∀ b ∈ Set.Icc (P.lo x0) (P.Rhi + P.Δ),
      P.zeta m b x0 p = (1 - P.β) ^ m * P.Fe (b - P.Δ) ^ (m - 1) * (P.Fe (p - P.Δ) ^ m)⁻¹ *
        P.fe (b - P.Δ) * (P.H b - P.L m b x0)) ∧
    (∀ b ∈ Set.Ioi (P.Rhi + P.Δ),
      P.zeta m b x0 p = (1 - P.β) ^ m * (P.Fe (p - P.Δ) ^ m)⁻¹ ∧ 0 < P.zeta m b x0 p) := by sorry

end PostQual.Incumbent
