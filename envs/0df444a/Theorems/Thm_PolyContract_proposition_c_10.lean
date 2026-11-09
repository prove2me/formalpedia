-- Prove2me | Theorems.Thm_PolyContract_proposition_c_10
-- name    : PolyContract.proposition_c_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:52:20.988781+00:00
-- url     : https://prove2.me/theorems/a853f0e7-cb66-4e85-9f95-b3c8f0d24d91
-- title:
--   Proposition C.10 — the base: table of marginals and rewards, (B1)–(B3)
-- statement:
--   Let $E_0=\{C_0,C_1,C_2\}$, $m=(5,12,4)$, $\beta=(1,4,4)$ and $f_0$ as in the base instance. Then $f_0$ is a polymatroid rank function, given by the cut form with arcs $C_0\to C_1$ (capacity $1/3$), $C_1\to C_2$ (capacity $1/2$) and weights $0,2/3,2/3$. Its full-plane best response $\xi^{(0)}$ has marginals $\rho$ and reward $r(\xi^{(0)}(\alpha))$:
--
--   | piece | $\rho_{C_0}$ | $\rho_{C_1}$ | $\rho_{C_2}$ | $r(\xi^{(0)}(\alpha))$ |
--   |---|---|---|---|---|
--   | $(-\infty,-1/6]$ | $5\alpha-1/3$ | $12\alpha-4/3$ | $4\alpha-8/3$ | $25/3$ |
--   | $[-1/6,1/3]$ | $5\alpha-1/3$ | $8\alpha-2$ | $8\alpha-2$ | $8\alpha+29/3$ |
--   | $[1/3,3/7]$ | $5\alpha-1/3$ | $12\alpha-10/3$ | $4\alpha-2/3$ | $37/3$ |
--   | $[3/7,2/3]$ | $32\alpha/5-14/15$ | $32\alpha/5-14/15$ | $4\alpha-2/3$ | $49\alpha/5+122/15$ |
--   | $[2/3,\infty)$ | $5\alpha$ | $12\alpha-14/3$ | $4\alpha-2/3$ | $44/3$ |
--
--   With $\zeta_1=1/3$, $\zeta_2=2/3$, $L_0(\alpha)=10+7\alpha$, $\varepsilon_0=1/30$, $R_0=3/10$:
--
--   1. (B1) the slopes of $\alpha\mapsto r(\xi^{(0)}(\alpha))$ on the five pieces are $0,8,0,49/5,0$;
--   2. (B2) on $[-1/6,\infty)$, $L_0\ge r(\xi^{(0)})$ with equality exactly at $\zeta_1,\zeta_2$; on $[-1/6,\zeta_1]$ the gap is $\zeta_1-\alpha$; for $\alpha\ge R_0$ the gap is at least $\operatorname{dist}(\alpha,\{\zeta_1,\zeta_2\})$; the gap is $\varepsilon_0$ at $R_0$ and $7\varepsilon_0$ at $\zeta_2+\varepsilon_0$;
--   3. (B3) on $(-7/3,\zeta_1]$, $\rho_{C_0}$ is the strict maximum of the marginals, and $\rho(R_0)=(7/6,2/5,2/5)$, so $\max_e\rho_e(R_0)=\rho_{C_0}(R_0)=7/6$.
--
--   This is level 0 of the comb gadget.
--
--   Differences from the source:
--   - encoding: the table and (B3) as values of ξ(0) on each closed piece; (B1) slopes → for every full-plane best response at a share of the closed piece; (B1) as r(α′) − r(α) = s(α′ − α) on the piece; reason: ξ(0) is unique (§B.6.1); a difference quotient states the slope of an affine piece
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Proposition C.10, p.56 (PDF p.57)

import Mathlib
import Definitions.Def_PolyContract_FullPlane
import Definitions.Def_PolyContract_BaseInstance

set_option autoImplicit false

namespace PolyContract

/-- **Proposition C.10** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, p.56): the base. On `E₀ = {C₀, C₁, C₂}` with `m = (5, 12, 4)`,
`β = (1, 4, 4)` and the values of `f₀` given there, `f₀` is a polymatroid rank function, given by
the cut form with the arcs `C₀ → C₁` of capacity `1/3`, `C₁ → C₂` of capacity `1/2` and the
weights `0, 2/3, 2/3`. Its full-plane best response `ξ^{(0)}` has the marginals `ρ` and the
reward `r(ξ^{(0)}(α))` of the table:

| piece | `ρ_{C₀}` | `ρ_{C₁}` | `ρ_{C₂}` | `r(ξ^{(0)}(α))` |
|---|---|---|---|---|
| `(−∞, −1/6]` | `5α − 1/3` | `12α − 4/3` | `4α − 8/3` | `25/3` |
| `[−1/6, 1/3]` | `5α − 1/3` | `8α − 2` | `8α − 2` | `8α + 29/3` |
| `[1/3, 3/7]` | `5α − 1/3` | `12α − 10/3` | `4α − 2/3` | `37/3` |
| `[3/7, 2/3]` | `32α/5 − 14/15` | `32α/5 − 14/15` | `4α − 2/3` | `49α/5 + 122/15` |
| `[2/3, ∞)` | `5α` | `12α − 14/3` | `4α − 2/3` | `44/3` |

With `ζ₁ := 1/3`, `ζ₂ := 2/3`, `L₀(α) := 10 + 7α`, `ε₀ := 1/30`, `R₀ := 3/10`:
(B1) the slopes of `α ↦ r(ξ^{(0)}(α))` on the five pieces are `0, 8, 0, 49/5, 0`;
(B2) on `[−1/6, ∞)`, `L₀ ≥ r(ξ^{(0)})` with equality exactly at `ζ₁` and `ζ₂`; on `[−1/6, ζ₁]`,
`L₀(α) − r(ξ^{(0)}(α)) = ζ₁ − α`; `L₀(α) − r(ξ^{(0)}(α)) ≥ dist(α, {ζ₁, ζ₂})` for `α ≥ R₀`; the gap
is `ε₀` at `R₀` and `7ε₀` at `ζ₂ + ε₀`;
(B3) on `(−7/3, ζ₁]`, `ρ_{C₀}` is the strict maximum of the three marginals, and
`ρ(R₀) = (7/6, 2/5, 2/5)`, so `max_e ρ_e(R₀) = ρ_{C₀}(R₀) = 7/6`.

**Formalization Note** `C₀, C₁, C₂` are `0, 1, 2 : Fin 3`. The table is stated for every
full-plane best response `y` at a share of the closed piece (the full-plane best response exists
and is unique, App. B.6.1). `r(ξ^{(0)}(α))` is `fpReward`. (B1) is stated as
`r(α′) − r(α) = s (α′ − α)` for shares `α, α′` of the piece with slope `s`. -/
theorem proposition_c_10 :
    let I := baseInstance
    let r := I.fpReward
    let ρ := fun (α : ℝ) (y : Fin 3 → ℝ) => I.marginal α y
    -- `f₀` is a rank function given by the cut form
    (IsRankFunction f0 ∧ baseCutForm.IsValid ∧ ∀ S, f0 S = (baseCutForm.cutFn S : ℝ)) ∧
    -- the table
    (∀ α ≤ (-1/6 : ℝ), ∀ y, I.IsFullPlaneBR α y →
      ρ α y 0 = 5 * α - 1/3 ∧ ρ α y 1 = 12 * α - 4/3 ∧ ρ α y 2 = 4 * α - 8/3 ∧
      I.reward y = 25/3) ∧
    (∀ α ∈ Set.Icc (-1/6 : ℝ) (1/3), ∀ y, I.IsFullPlaneBR α y →
      ρ α y 0 = 5 * α - 1/3 ∧ ρ α y 1 = 8 * α - 2 ∧ ρ α y 2 = 8 * α - 2 ∧
      I.reward y = 8 * α + 29/3) ∧
    (∀ α ∈ Set.Icc (1/3 : ℝ) (3/7), ∀ y, I.IsFullPlaneBR α y →
      ρ α y 0 = 5 * α - 1/3 ∧ ρ α y 1 = 12 * α - 10/3 ∧ ρ α y 2 = 4 * α - 2/3 ∧
      I.reward y = 37/3) ∧
    (∀ α ∈ Set.Icc (3/7 : ℝ) (2/3), ∀ y, I.IsFullPlaneBR α y →
      ρ α y 0 = 32 * α / 5 - 14/15 ∧ ρ α y 1 = 32 * α / 5 - 14/15 ∧ ρ α y 2 = 4 * α - 2/3 ∧
      I.reward y = 49 * α / 5 + 122/15) ∧
    (∀ α ≥ (2/3 : ℝ), ∀ y, I.IsFullPlaneBR α y →
      ρ α y 0 = 5 * α ∧ ρ α y 1 = 12 * α - 14/3 ∧ ρ α y 2 = 4 * α - 2/3 ∧
      I.reward y = 44/3) ∧
    -- (B1)
    ((∀ α ≤ (-1/6 : ℝ), ∀ α' ≤ (-1/6 : ℝ), r α' - r α = 0 * (α' - α)) ∧
      (∀ α ∈ Set.Icc (-1/6 : ℝ) (1/3), ∀ α' ∈ Set.Icc (-1/6 : ℝ) (1/3),
        r α' - r α = 8 * (α' - α)) ∧
      (∀ α ∈ Set.Icc (1/3 : ℝ) (3/7), ∀ α' ∈ Set.Icc (1/3 : ℝ) (3/7),
        r α' - r α = 0 * (α' - α)) ∧
      (∀ α ∈ Set.Icc (3/7 : ℝ) (2/3), ∀ α' ∈ Set.Icc (3/7 : ℝ) (2/3),
        r α' - r α = 49/5 * (α' - α)) ∧
      (∀ α ≥ (2/3 : ℝ), ∀ α' ≥ (2/3 : ℝ), r α' - r α = 0 * (α' - α))) ∧
    -- (B2)
    ((∀ α ≥ (-1/6 : ℝ), r α ≤ baseLine α ∧ (r α = baseLine α ↔ α = 1/3 ∨ α = 2/3)) ∧
      (∀ α ∈ Set.Icc (-1/6 : ℝ) (1/3), baseLine α - r α = 1/3 - α) ∧
      (∀ α ≥ (3/10 : ℝ), Metric.infDist α {1/3, 2/3} ≤ baseLine α - r α) ∧
      baseLine (3/10) - r (3/10) = 1/30 ∧ baseLine (2/3 + 1/30) - r (2/3 + 1/30) = 7 * (1/30)) ∧
    -- (B3)
    ((∀ α ∈ Set.Ioc (-7/3 : ℝ) (1/3), ∀ y, I.IsFullPlaneBR α y →
        ρ α y 1 < ρ α y 0 ∧ ρ α y 2 < ρ α y 0) ∧
      ∀ y, I.IsFullPlaneBR (3/10) y →
        ρ (3/10) y 0 = 7/6 ∧ ρ (3/10) y 1 = 2/5 ∧ ρ (3/10) y 2 = 2/5 ∧
        ∀ e, ρ (3/10) y e ≤ ρ (3/10) y 0) := by sorry

end PolyContract
