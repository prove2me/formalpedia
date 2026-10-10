-- Prove2me | Theorems.Thm_ThomsonN7_Final_capspec_cap
-- name    : ThomsonN7.Final.capspec_cap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T01:46:14.878351+00:00
-- url     : https://prove2.me/theorems/0ca42065-5a4d-4c87-9515-b15dd415e3b1
-- title:
--   Thomson $N=7$: the cap certificate satisfies the cap specification at $a_0=-\tfrac{99}{100}$
-- statement:
--   Let $\varphi(t)=(2-2t)^{-1/2}$, let $P$ be the pentagonal bipyramid and $E$ the Coulomb energy, and write $c_1=\cos\tfrac{2\pi}5$, $c_2=\cos\tfrac{4\pi}5$. The *cap specification* at $a_0=-\tfrac{99}{100}$ holds: there are reals $e,\delta,\tau$ and functions $H_A,H_B,H_C:\mathbb R\to\mathbb R$ such that
--
--   1. $\tau\le\tfrac1{165000}$ and $E(P)\le e+\delta$;
--   2. for every configuration $y$ of seven distinct unit vectors in $\mathbb R^3$ in which the pair $(0,1)$ realises the smallest inner product and $\langle y_0,y_1\rangle\le a_0$,
--
--   $$e\ \le\ \sum_{i<j}H_{\mathrm{cls}(i,j)}(\langle y_i,y_j\rangle),$$
--
--      where $\mathrm{cls}(i,j)$ is $A$ for the pair $\{0,1\}$, $B$ for pairs meeting $\{0,1\}$ in one point, and $C$ otherwise;
--   3. $H_A\le\varphi$ on $[-1,a_0]$ and $\varphi(t)-H_A(t)\le\delta\Rightarrow|t+1|\le\tau$ there;
--   4. $H_B\le\varphi$ on $[-1,1)$ and $\varphi(t)-H_B(t)\le\delta\Rightarrow|t|\le\tau$ there;
--   5. $H_C\le\varphi$ on $[-1,1)$ and $\varphi(t)-H_C(t)\le\delta\Rightarrow|t-c_1|\le\tau$ or $|t-c_2|\le\tau$ there.
--
--   This is the certificate half of the cap cell in the proof of the Thomson problem for seven electrons: combined with the soundness theorem `ThomsonN7.Glue.capSpec_sound` it gives $E(P)\le E(y)$ on the cap.
--
--   **Formalization Note** `Glue.CapSpec` and the data of the certificate `tc_cap` are the platform definitions `ThomsonN7_core` and `ThomsonN7_cap_data_1/2`, taken verbatim from the source.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2; Lean `ThomsonN7.Final.capspec_cap`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L16169; definition of `CapSpec` at https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L12717

import Definitions.Def_ThomsonN7_core
import Definitions.Def_ThomsonN7_cap_data_2

namespace ThomsonN7

theorem Final.capspec_cap : Glue.CapSpec (-99 / 100 : ℝ) := by sorry

end ThomsonN7
