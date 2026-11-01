-- Prove2me | Theorems.Thm_SponsoredAssort_corollary_5_1
-- name    : SponsoredAssort.corollary_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:06.641991+00:00
-- url     : https://prove2.me/theorems/37018cd4-1810-4940-87be-0056adef9ee9
-- title:
--   Corollary 5.1 — an IC mechanism must keep $S$ on an interval of reports (corrected: $y\ge v_i$, no ties)
-- statement:
--   Let $m$ satisfy (IC). Fix a seller $i$ with $r_i>0$, a profile $v\in\mathbb R^n_+$ and an assortment $S\ni i$ with $S=S(v_i,v_{-i})$, and write $a(S')=1+\sum_{j\in S'\setminus\{i\}}v_j$. Assume
--
--   1. $0<v_i<\sqrt{a(S)a(S')}$ for every $S'\in\mathrm{supp}_i(m,v_{-i})$ with $i\in S'$;
--   2. no $S'\in\mathrm{supp}_i(m,v_{-i})$ with $i\in S'$ and $S'\ne S$ has $a(S')=a(S)$.
--
--   Let $\underline{\mathcal S}=\{S'\in\mathrm{supp}_i(m,v_{-i}):a(S')<a(S),\,i\in S'\}$ and $\bar{\mathcal S}=\{S'\in\mathrm{supp}_i(m,v_{-i}):a(S')>a(S),\,i\in S'\}$. Then $S=S(y,v_{-i})$ for every $y\ge v_i$ with
--
--   $$
--   \frac{1}{v_i}\,a(S)\,a(S')<y\ \ \text{for all }S'\in\underline{\mathcal S},\qquad y<\frac{1}{v_i}\,a(S)\,a(S')\ \ \text{for all }S'\in\bar{\mathcal S}.
--   $$
--
--   If an IC mechanism displays $S$ to seller $i$ at a low attractiveness, it must keep displaying $S$ over a whole interval above it; this is the distortion at the top that drives the upper bound of Proposition 5.4.
--
--   Differences from the source:
--   - correction: $S=S(y,v_{-i})$ for all $y$ in the printed range → only for $y\ge v_i$; reason: the proof drops $y>v_i$ using an element of $\underline{\mathcal S}$, which may be empty: for $n=2$, $r=(1,1)$, $m^{\downarrow}$, $v=(1/2,1/4)$, $i=1$, both families are empty, but $S(0.1,1/4)=\{2\}\ne\{1\}$
--   - correction: no hypothesis on ties → no $S'\ne S$ in the support with $i\in S'$ has $a(S')=a(S)$; reason: the proof's cases omit ties: the zero-payment mechanism on three sellers with $S(v)=\{1,2,3\}$ if $v_3>0$ or $v_1\ge1$ and $\{1,2\}$ otherwise is IC and IR, satisfies the printed hypotheses at $v=(1/2,1,0)$, $i=1$, and displays $\{1,2,3\}$ at $y=2$
--   - reading: $1/v_1$ in the display → $1/v_i$; reason: typo; the proof uses $v_i$
--   - encoding: $a(S)\sup_{\underline{\mathcal S}}a(S')/v_i<y<a(S)\inf_{\bar{\mathcal S}}a(S')/v_i$ → the bound for every member of each family; reason: equivalent for finite families; an empty family imposes no bound
--   - generalization: standing revenues $r_1\ge\dots\ge r_n>0$ → only $r_i>0$; reason: the proof uses only $r_i>0$; it specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Corollary 5.1, p.25 (proof: Appendix G.1, OA pp.36–37)

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_supp
import Definitions.Def_SponsoredAssort_others

open scoped NNReal

namespace SponsoredAssort

/-- **Corollary 5.1** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), p.25), corrected. Let `m`
satisfy (IC). Fix a seller `i` with `rᵢ > 0`, a profile `v ∈ ℝⁿ₊` and an assortment `S ∋ i` with
`S = S(vᵢ, v₋ᵢ)`, and write `a(S') = 1 + ∑_{j ∈ S' \ {i}} vⱼ`. Assume
`0 < vᵢ < √(a(S)a(S'))` for every `S' ∈ suppᵢ(m, v₋ᵢ)` with `i ∈ S'`, and that no such `S' ≠ S`
has `a(S') = a(S)`. Then `S = S(y, v₋ᵢ)` for every `y ≥ vᵢ` with
`a(S)a(S')/vᵢ < y` for all `S' ∈ 𝒮̲ = {S' ∈ suppᵢ(m, v₋ᵢ) : a(S') < a(S), i ∈ S'}` and
`y < a(S)a(S')/vᵢ` for all `S' ∈ 𝒮̄ = {S' ∈ suppᵢ(m, v₋ᵢ) : a(S') > a(S), i ∈ S'}`.

**Formalization Note.** Corrections of the printed statement: (a) `y ≥ vᵢ` is required — with
`n = 2`, `r = (1, 1)`, `m↓`, `v = (1/2, 1/4)`, `i = 1` both `𝒮̲` and `𝒮̄` are empty and the
printed range is all of `ℝ₊`, but `S(0.1, 1/4) = {2}`; (b) ties `a(S') = a(S)`, `S' ≠ S` are
excluded — the zero-payment mechanism on three sellers with `S(v) = {1,2,3}` if `v₃ > 0` or
`v₁ ≥ 1` and `S(v) = {1,2}` otherwise is IC, satisfies the printed hypotheses at
`v = (1/2, 1, 0)`, `i = 1`, but `S(2, 1, 0) = {1,2,3}`. The printed `1/v₁` is read as `1/vᵢ`, and
the bounds by `sup 𝒮̲`, `inf 𝒮̄` are written as bounds for every member (so an empty family imposes
nothing). -/
theorem corollary_5_1 {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (hIC : IsIC r m) (i : Fin n)
    (hr : 0 < r i) (v : Attr n) (S : Finset (Fin n)) (hS : m.alloc v = S) (hiS : i ∈ S)
    (hvi : 0 < v i)
    (hsq : ∀ T ∈ supp m i v, i ∈ T → (v i : ℝ) ^ 2 < others v i S * others v i T)
    (htie : ∀ T ∈ supp m i v, i ∈ T → T ≠ S → others v i T ≠ others v i S)
    (y : ℝ≥0) (hy : v i ≤ y)
    (hlo : ∀ T ∈ supp m i v, i ∈ T → others v i T < others v i S →
      others v i S * others v i T / (v i : ℝ) < y)
    (hhi : ∀ T ∈ supp m i v, i ∈ T → others v i S < others v i T →
      (y : ℝ) < others v i S * others v i T / (v i : ℝ)) :
    m.alloc (Function.update v i y) = S := by sorry

end SponsoredAssort
