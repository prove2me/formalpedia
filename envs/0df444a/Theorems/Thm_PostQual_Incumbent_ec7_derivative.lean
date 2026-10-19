-- Prove2me | Theorems.Thm_PostQual_Incumbent_ec7_derivative
-- name    : PostQual.Incumbent.ec7_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:19.546511+00:00
-- url     : https://prove2.me/theorems/a844d6f8-f932-4495-b626-425986fd4dd7
-- title:
--   (EC.7), p. ec5 (PDF 39) — ∂Π^m_0(b;x0,p)/∂b and its bound ζ^m(b;x0,p)
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Let $x_0\in[\underline R,\overline R]$, $1\le m\le N$, $p>\ell(x_0)$, and $b>\ell(x_0)$ with $b\ne\overline R+\Delta$. Then $b\mapsto\Pi^m_0(b;x_0,p)$ is differentiable at $b$ with
--   $$\frac{\partial\Pi^m_0(b;x_0,p)}{\partial b}=\frac{[F_e(b-\Delta)]^{m-1}(1-\beta)^m}{[F_e(p-\Delta)]^m}\Big\{-m\Big[\frac{V^{m-1}_0(x_0,b)}{(1-\beta)^m}-(b-x_0)\Big]f_e(b-\Delta)+F_e(b-\Delta)\Big\}\le\zeta^m(b;x_0,p).$$
--
--   This is the derivative formula on which the whole proof of Theorem 2 rests: the sign of $\zeta^m$ controls where $\Pi^m_0$ increases.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The point $b=\overline R+\Delta$, where $f_e(b-\Delta)$ jumps to $0$ and $\Pi^m_0$ has a kink, and the left end $b=\ell(x_0)$ are excluded; the page also lists them without comment. $b$ may exceed $p$ (signed integral).
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec5 (PDF 39), proof of Theorem 2, (EC.7)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- (EC.7), p. ec5: the derivative of `Π^m_0(b; x0, p)` in `b`, and its upper bound `ζ^m(b; x0, p)`,
at every `b > max{R̲+∆, x0}` other than the kink `b = R̄ + ∆`. -/
theorem ec7_derivative (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (p : ℝ) (hp : P.lo x0 < p) (b : ℝ) (hb : P.lo x0 < b) (hbk : b ≠ P.Rhi + P.Δ) :
    HasDerivAt (fun b' => P.Pi m b' x0 p)
      (P.Fe (b - P.Δ) ^ (m - 1) * (1 - P.β) ^ m / P.Fe (p - P.Δ) ^ m *
        (-(m : ℝ) * (P.V (m - 1) x0 b / (1 - P.β) ^ m - (b - x0)) * P.fe (b - P.Δ) +
          P.Fe (b - P.Δ))) b ∧
    deriv (fun b' => P.Pi m b' x0 p) b ≤ P.zeta m b x0 p := by sorry

end PostQual.Incumbent
