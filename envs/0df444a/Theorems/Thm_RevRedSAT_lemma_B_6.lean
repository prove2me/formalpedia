-- Prove2me | Theorems.Thm_RevRedSAT_lemma_B_6
-- name    : RevRedSAT.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:33.276714+00:00
-- url     : https://prove2.me/theorems/0778b6ba-e493-444c-b8e6-568223953b81
-- title:
--   Lemma B.6 — the core and petal branches decrease the measure
-- statement:
--   Under the standing assumptions of App. B, let $\mathcal F$ be reduced and not sparse; let $s$ be the smallest layer size containing an eligible flower, $p$ the smallest eligible petal size in that layer, and $\mathcal Z$ an eligible flower in $\mathcal F_s$ with petal size $p$ and core $C$, $c=s-p=|C|$. Then
--
--   1. no member of $\mathcal F$ is contained in $C$ or in any petal of $\mathcal Z$;
--   2. the layers $\mathcal F_c\cup\{C\}$ and $\mathcal F_p\cup P(\mathcal Z)$ are almost sparse;
--   3. the core and petal branches decrease the measure by at least $\Delta_C=w_c/2$ and $\Delta_P=w_pt_p/2$:
--
--   $$\mu(\mathrm{reduce}(\mathcal F\cup\{C\}))\le\mu(\mathcal F)-\Delta_C,\qquad \mu(\mathrm{reduce}(\mathcal F\cup P(\mathcal Z)))\le\mu(\mathcal F)-\Delta_P.$$
--
--   Differences from the source:
--   - encoding: δ = 2^{−j}, weights (17), measure (18) → j : ℕ; real-valued w_s, t_p, µ; reason: same quantities
--   - encoding: decrease the measure by at least ∆ → µ(child) ≤ µ(F) − ∆; reason: the meaning of the phrase
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.6, p.89 (printed) = PDF p.91; recursive step (19), p.88

import Mathlib
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma B.6 (both branches decrease the measure).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.6, p.89: "No member of F is contained in C or in any petal of Z. The layers F_c ∪ {C}
and F_p ∪ P(Z) are almost sparse. Consequently, the core and petal branches decrease the measure by
at least ∆C = w_c/2 and ∆P = w_p t_p/2, respectively."

Context (recursive step, p.88; p.88 before the lemma): `F` is reduced and not sparse; `s` is the
smallest layer size containing an eligible flower, `p` the smallest eligible petal size in that layer,
`Z` an eligible flower in `F_s` with petal size `p` and core `C`, and `c = s − p = |C|`; standing
assumptions of App. B (p.87). The two children are `F_C = reduce(F ∪ {C})` and
`F_P = reduce(F ∪ P(Z))` ((19), p.88).

**Formalization Note** "Decrease by at least ∆" means `µ(child) ≤ µ(F) − ∆`. Non-sparseness of `F`
is implied by the eligible flower `Z`. -/
theorem lemma_B_6 (d j n k s : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hk : 0 < k)
    (F : Finset (Finset (Fin n))) (hrank : ∀ S ∈ F, S.card ≤ d) (hne : ∀ S ∈ F, S.Nonempty)
    (hred : IsReduced F) (Z : Finset (Finset (Fin n))) (hZ : IsEligible d j F s Z)
    (hs : ∀ s' < s, ∀ Z', ¬ IsEligible d j F s' Z')
    (hp : ∀ Z', IsEligible d j F s Z' → s - (core Z).card ≤ s - (core Z').card) :
    (∀ S ∈ F, ¬ S ⊆ core Z) ∧ (∀ S ∈ F, ∀ P ∈ petals Z, ¬ S ⊆ P) ∧
    AlmostSparseLayer d j (F ∪ {core Z}) (core Z).card ∧
    AlmostSparseLayer d j (F ∪ petals Z) (s - (core Z).card) ∧
    mu d j k (reduceFam (F ∪ {core Z})) ≤ mu d j k F - ws d j (core Z).card / 2 ∧
    mu d j k (reduceFam (F ∪ petals Z)) ≤
      mu d j k F - ws d j (s - (core Z).card) * tp d j (s - (core Z).card) / 2 := by sorry

end RevRedSAT
