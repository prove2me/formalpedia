-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_D_22
-- name    : PFRelease.Supplement.theorem_D_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:48:27.272123+00:00
-- url     : https://prove2.me/theorems/ab937aa8-e07c-4443-89e9-13cfd40ae014
-- title:
--   Theorem D.22 — private all-pairs effective resistance retains every edge and has relative error $\le\alpha$
-- statement:
--   Let $V$ be a public vertex set with $v:=|V|\ge2$, recorded as in §D.4: one slot for every unordered pair $\{u,u'\}$, holding $x_e=\sqrt{w_e}(\chi_u-\chi_{u'})$ with $w_e\ge0$ (an absent edge is the ordinary zero record), plus a public number of zero padding records; $n$ counts all slots. Let $n,b\in\mathbb N$ with $n/b\in\mathbb N$; $\alpha\in(0,1)$; $\varepsilon\in(0,1]$; $\delta\in(0,1)$; and $\beta_B,\beta_F,\beta_Q>0$ with $\beta:=\beta_B+\beta_F+\beta_Q<1$ and $\delta\le8\beta_F$. Put
--   $$
--   m:=\frac nb,\quad L:=\ln(16/\delta),\quad J_Q:=\ln(v^2/\beta_Q),\quad r:=\Big\lceil\frac{8J_Q}{\alpha^2}\Big\rceil,\quad \tau:=\frac{2(\sqrt{rL}+L)}{n\varepsilon}.
--   $$
--   Suppose
--   $$
--   m\ge\max\Big\{\frac{400L^2}{\varepsilon^{3/2}},\ \frac{1800L\ln(2n/\beta_F)}{\varepsilon^{3/2}}\Big\},
--   $$
--   and the input is a connected graph $G$, given as $n$ records without null records, whose maximum leverage $\ell_{\max}:=\max_{e:w_e>0}w_eR_{\mathrm{eff},G}(u,u')$ satisfies (9):
--   $$
--   \ell_{\max}\le\frac{\varepsilon}{8(\sqrt{rL}+L)}\qquad\text{and}\qquad m(v-1)\exp\Big(-\frac1{8m\ell_{\max}}\Big)\le\beta_B.
--   $$
--   Then with probability at least $1-\beta$, the filter of $\mathrm{PFR}_b^{\varepsilon,\delta}(M_{\mathrm{pot}},\varphi_0,\tau)$ with $r$ potential vectors retains every record, and every pair of distinct vertices $u,u'$ satisfies
--   $$
--   \big|\widehat R_{\mathrm{eff}}(u,u')-R_{\mathrm{eff},G}(u,u')\big|\le\alpha\,R_{\mathrm{eff},G}(u,u').
--   $$
--
--   The filter is that of Theorem 4.5 ($t=7n/(8b)$, $\sigma_F=12/\varepsilon$, $\sigma_F'=108L/\varepsilon^{3/2}$, $\kappa=2\sigma_FL$) testing $F_{2\tau}(\varphi_0)$, with the zero-ridge score $\varphi_0$. On well-connected graphs, no single edge supplies much connectivity, and the mechanism estimates every resistance to relative error $\alpha$ without knowing $\ell_{\max}$ or a bound on the weights.
--
--   **Formalization Note** Weights are a symmetric nonnegative function $w$ on pairs of vertices; a slot map puts every unordered pair of distinct vertices in exactly one slot (in either orientation) and the remaining slots are padding. Connectivity is that of the graph of positive-weight pairs. $\mathbf L_G=\sum_ex_ex_e^T$, $R_{\mathrm{eff},G}$ uses the Moore–Penrose pseudoinverse, and $\ell_{\max}$ is a supremum over the finite, nonempty set of positive-weight pairs. Because the input has no null records, "retains every record" means the filter nulls the empty set, on which the release is $M_{\mathrm{pot}}(s)$; the probability of the joint event is the probability that the filter nulls nothing times $M_{\mathrm{pot}}(s)$ of the accuracy event.
--
--   Differences from the source:
--   - encoding: a connected graph on the public vertices, given as n records without null records (one slot per unordered pair holding √w_e(χ_u − χ_u′), absent edges as zero records, zero padding) → w : V → V → ℝ symmetric and nonnegative, a slot map Fin n → Option (V × V) covering every unordered pair of distinct vertices exactly once, slot k holding some (edgeRec w (slot k)), padding as some 0, and the graph of positive-weight pairs connected; reason: the setting of §D.4 (p.50), with the orientation of each pair immaterial since every quantity is quadratic in the record
--   - encoding: ℓ_max := max_{e : w_e > 0} ℓ_e → the supremum of w u u′ · R_eff,G(u, u′) over pairs u ≠ u′ with w u u′ > 0; reason: a maximum over a finite set, nonempty since G is connected and v ≥ 2
--   - encoding: L_G^† → the matrix of the published Moore–Penrose pseudoinverse; reason: same matrix
--   - encoding: with probability at least 1 − β, the filter retains every record and every pair of distinct vertices satisfies the bound → filterLaw … s ∅ · M_pot(s){all pairs good} ≥ 1 − (β_B + β_F + β_Q); reason: with no null records, retaining every record is I = ∅, on which the PFR release is M_pot(s); this is the probability of the joint event
--   - encoding: PFR^{ε,δ}_b, r = ⌈8J_Q/α²⌉ → the filter of Theorem 4.5 with t, κ, σ_F, σ_F′ of p.13 testing predOf φ_0 (2τ); Nat.ceil; reason: the definition of PFR^{ε,δ}_b on p.13; Lean convention
--   - encoding: n/b ∈ ℕ → hypotheses 0 < b and b ∣ n; reason: same instances
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.22 and (9), p.52 (PDF p.54); §D.4 Setting, p.50 (PDF p.52); §5.4, eq. (4), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_filterLaw
import Definitions.Def_PFRelease_Supplement_phiLam
import Definitions.Def_PFRelease_Supplement_potMech

open MeasureTheory ProbabilityTheory Matrix

namespace PFRelease.Supplement

/-- **Theorem D.22 (Utility of private all-pairs effective resistance)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.22,
p.52 = PDF p.54). Given `n, b ∈ ℕ` with `n/b ∈ ℕ`; `α ∈ (0, 1)`; `ε ∈ (0, 1]`; `δ ∈ (0, 1)`; and
`β_B, β_F, β_Q > 0` with `β := β_B + β_F + β_Q < 1` and `δ ≤ 8β_F`, if
`m ≥ max{400L²/ε^{3/2}, 1800L ln(2n/β_F)/ε^{3/2}}` and the input is a connected graph `G` on the public
vertices, given as `n` records without null records, whose maximum leverage `ℓ_max` satisfies (9),
`ℓ_max ≤ ε/(8(√(rL) + L))` and `m(v − 1) exp(−1/(8mℓ_max)) ≤ β_B`, then with probability at least
`1 − β`, the filter of `PFR_b^{ε,δ}(M_pot, φ_0, τ)` with `r` potential vectors retains every record, and
every pair of distinct vertices `u, u′` satisfies `|R̂_eff(u, u′) − R_eff,G(u, u′)| ≤ α R_eff,G(u, u′)`,
where `v` is the number of vertices, `m := n/b`, `L := ln(16/δ)`, `J_Q := ln(v²/β_Q)`,
`r := ⌈8J_Q/α²⌉` and `τ := 2(√(rL) + L)/(nε)`.

**Formalization Note**
* Setting of §D.4 (p.50): a public finite vertex set `V` with `v = |V| ≥ 2`; edge weights
  `w u u′ = w u′ u ≥ 0`; the slot map `slot` puts every unordered pair `{u, u′}` (`u ≠ u′`) in exactly one
  slot (in either orientation) and fills the other slots with padding (`none`). Slot `k` holds the
  non-null record `x_e = √w_e (χ_u − χ_{u′})` (`edgeRec`), an absent edge or padding being the ordinary
  zero record. `G` is connected: the graph of positive-weight pairs is connected.
* `L_G = Σ_e x_e x_eᵀ` is `gram` of the dataset, `R_eff,G` uses the Moore–Penrose pseudoinverse
  `pinv`, `ℓ_e = w_e R_eff,G(u, u′)` and `ℓ_max` is the maximum over pairs with `w_e > 0` (a supremum over a
  finite nonempty index type). `φ_0` is `phiLam 0` (zero-ridge leverage `|s| xᵀL_s†x` on `range(L_s)`,
  `∞` off it). The filter is that of Theorem 4.5 (`t = 7n/(8b)`, `σ_F = 12/ε`, `σ_F′ = 108L/ε^{3/2}`,
  `κ = 2σ_F L`) testing `F_{2τ}(φ_0)`. "Retains every record" is `I = ∅` (no null records), on which
  the release is `M_pot(s)`; the joint probability is `filterLaw … s ∅ · M_pot(s){…}`.
* `r` is the natural-number ceiling; `b > 0`, `b ∣ n` encode `n/b ∈ ℕ`. -/
theorem theorem_D_22 {V : Type*} [Fintype V] [DecidableEq V] (hv : 2 ≤ Fintype.card V)
    (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (α ε δ βB βF βQ : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hβB : 0 < βB) (hβF : 0 < βF) (hβQ : 0 < βQ) (hβ : βB + βF + βQ < 1) (hδβ : δ ≤ 8 * βF)
    (w : V → V → ℝ) (hw0 : ∀ u u', 0 ≤ w u u') (hwsymm : ∀ u u', w u u' = w u' u)
    (slot : Fin n → Option (V × V))
    (hslot_ne : ∀ (k : Fin n) (u u' : V), slot k = some (u, u') → u ≠ u')
    (hslot_cover : ∀ u u' : V, u ≠ u' →
      ∃! k : Fin n, slot k = some (u, u') ∨ slot k = some (u', u))
    (hconn : (SimpleGraph.fromRel fun u u' => 0 < w u u').Connected) :
    let s : Fin n → Option (EuclideanSpace ℝ V) := fun k => some (edgeRec w (slot k))
    let LG := gram (toList s)
    let ℓmax : ℝ := ⨆ p : {p : V × V // p.1 ≠ p.2 ∧ 0 < w p.1 p.2},
      w p.1.1 p.1.2 * effRes LG p.1.1 p.1.2
    let v : ℝ := Fintype.card V
    let m : ℝ := (n : ℝ) / b
    let L := Real.log (16 / δ)
    let JQ := Real.log (v ^ 2 / βQ)
    let r : ℕ := ⌈8 * JQ / α ^ 2⌉₊
    let τ := 2 * (Real.sqrt (r * L) + L) / (n * ε)
    let t := 7 * (n : ℝ) / (8 * (b : ℝ))
    let σF := 12 / ε
    let σF' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σF * L
    max (400 * L ^ 2 / ε ^ (3 / 2 : ℝ)) (1800 * L * Real.log (2 * n / βF) / ε ^ (3 / 2 : ℝ)) ≤ m →
    ℓmax ≤ ε / (8 * (Real.sqrt (r * L) + L)) →
    m * (v - 1) * Real.exp (-1 / (8 * m * ℓmax)) ≤ βB →
    ENNReal.ofReal (1 - (βB + βF + βQ)) ≤
      filterLaw b t κ σF σF' (predOf (phiLam 0) (2 * τ)) s ∅ *
        potMech r s {Y | ∀ u u' : V, u ≠ u' →
          |effResHat Y u u' - effRes LG u u'| ≤ α * effRes LG u u'} := by sorry

end PFRelease.Supplement
