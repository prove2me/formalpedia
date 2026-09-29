-- Prove2me | Theorems.Thm_PolyhedralSOC_Sandwich_feasible_set_sandwich
-- name    : PolyhedralSOC.Sandwich.feasible_set_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:54:29.400068+00:00
-- url     : https://prove2.me/theorems/6b0b04ed-9931-4592-8163-a9465ef3e52e
-- title:
--   Proposition 4.1 — γ(ε)x̄ + (1−γ(ε))Feas(CQP_ε) ⊆ Feas(CQP) ⊆ Feas(CQP_ε)
-- statement:
--   Let (CQP) be a conic quadratic problem with $m\ge1$ conic constraints
--   $$
--   \min_x\bigl\{e^Tx \bigm| Ax\ge b,\ \|A_\ell x-b_\ell\|_2\le c_\ell^Tx-d_\ell,\ \ell=1,\dots,m\bigr\},
--   $$
--   and let (CQP$_\varepsilon$) be its $\varepsilon$-relaxation, in which the right-hand sides are multiplied by $1+\varepsilon$. Assume that (CQP) is
--   1. **strictly feasible**: there exist $\bar x$ and $r>0$ with $A\bar x\ge b$ and $\|A_\ell\bar x-b_\ell\|_2\le[c_\ell^T\bar x-d_\ell]-r$ for $\ell=1,\dots,m$;
--   2. **semibounded**: there is $R$ such that every feasible $x$ of (CQP) satisfies $c_\ell^Tx-d_\ell\le R$ for $\ell=1,\dots,m$.
--
--   Then for every $\varepsilon>0$ with $\gamma(\varepsilon)\equiv R\varepsilon/r<1$,
--   $$
--   \gamma(\varepsilon)\bar x+(1-\gamma(\varepsilon))\,\mathrm{Feas}(\mathrm{CQP}_\varepsilon)\ \subseteq\ \mathrm{Feas}(\mathrm{CQP})\ \subseteq\ \mathrm{Feas}(\mathrm{CQP}_\varepsilon),
--   $$
--   where $\gamma\bar x+(1-\gamma)S=\{\gamma\bar x+(1-\gamma)y : y\in S\}$.
--
--   The result says that under these two conditions the feasible sets of (CQP) and of its relaxation are $O(\varepsilon)$-close: shrinking the relaxed feasible set towards $\bar x$ by the factor $1-\gamma(\varepsilon)$ lands inside the exact feasible set. Combined with a polyhedral $\varepsilon$-approximation of the Lorentz cone, it quantifies how well the resulting linear program approximates (CQP).
--
--   **Formalization Note** Two corrections of the printed statement. (a) In hypothesis (i) the page prints $[c_\ell^Tx-d_\ell]-r$ without the bar over $x$; the proof uses $\bar x$, as here. (b) The hypothesis $m\ge1$ is added: with no conic constraints hypothesis (ii) is vacuous, $R$ may be negative, and the left inclusion can fail (for $n=1$, $A=[1]$, $b=0$, $\bar x=1$, $y=0$, $R=-1$, $r=\varepsilon=1$ it produces the infeasible point $-1$). For $m\ge1$ the hypotheses force $R\ge r>0$, so $0<\gamma(\varepsilon)<1$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF 11), Proposition 4.1, (14)

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

namespace PolyhedralSOC.Sandwich

/-- **Proposition 4.1** (Ben-Tal & Nemirovski, *On Polyhedral Approximations of the
Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF p. 11)).
Assume that (CQP), with `m ≥ 1` conic constraints, is
(i) strictly feasible: there exist `x̄` and `r > 0` with `Ax̄ ≥ b`,
`‖A_ℓ x̄ − b_ℓ‖₂ ≤ [c_ℓᵀx̄ − d_ℓ] − r` for all `ℓ`;
(ii) semibounded: every feasible `x` of (CQP) has `c_ℓᵀx − d_ℓ ≤ R` for all `ℓ`.
Then for every `ε > 0` with `γ(ε) = Rε/r < 1`,
`(14)  γ(ε) x̄ + (1 − γ(ε)) Feas(CQP_ε) ⊂ Feas(CQP) ⊂ Feas(CQP_ε)`.
The left-hand side is the image of `Feas(CQP_ε)` under `y ↦ γ(ε) x̄ + (1 − γ(ε)) y`.
Corrections of the printed statement: in (i) the page prints `c_ℓᵀx` for `c_ℓᵀx̄` (the proof
uses `x̄`); `m ≥ 1` is added, since for `m = 0` hypothesis (ii) is vacuous, `R` may be
negative, and the left inclusion fails. -/
theorem feasible_set_sandwich {n k₀ m : ℕ} (P : CQP n k₀ m) (hm : 0 < m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (R : ℝ) (hii : IsSemibounded P R)
    (ε : ℝ) (hε : 0 < ε) (hγ : R * ε / r < 1) :
    (fun y => (R * ε / r) • xbar + (1 - R * ε / r) • y) '' feasRelaxed P ε ⊆ feas P ∧
      feas P ⊆ feasRelaxed P ε := by sorry

end PolyhedralSOC.Sandwich
