-- Prove2me | Theorems.Thm_RevRedSAT_lemma_B_5
-- name    : RevRedSAT.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:24.997852+00:00
-- url     : https://prove2.me/theorems/984071cc-af23-4ac9-a1d6-d6c856c8cbc3
-- title:
--   Lemma B.5 — adding shorter constraints decreases the measure by $(w_h/2)|\mathcal Q|$
-- statement:
--   Under the standing assumptions of App. B ($d\ge2$, $\delta=2^{-j}$, $j\ge2$, $k>0$, nonempty sets of size at most $d$), let $\mathcal F$ be reduced and $1\le h\le\tau(\mathcal F)$. Let $\mathcal Q$ be a family of distinct $h$-element sets such that no member of $\mathcal F$ is contained in any member of $\mathcal Q$. If $\mathcal F_h\cup\mathcal Q$ is almost sparse, then
--
--   $$\mu(\mathrm{reduce}(\mathcal F\cup\mathcal Q))\le\mu(\mathcal F)-\frac{w_h}{2}|\mathcal Q|.$$
--
--   Differences from the source:
--   - encoding: δ = 2^{−j}, weights (17), measure (18) → j : ℕ; real-valued w_s, t_p, µ; reason: same quantities
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.5, p.88 (printed) = PDF p.90

import Mathlib
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma B.5 (adding shorter constraints decreases the measure).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.5, p.88: "Let F be reduced and 1 ≤ h ≤ τ(F). Let Q be a family of distinct h-element
sets such that no member of F is contained in any member of Q. If F_h ∪ Q is almost sparse, then
µ(reduce(F ∪ Q)) ≤ µ(F) − (w_h/2)|Q|."

Under the standing assumptions of App. B (p.87: `d ≥ 2`, `δ = 2^{−j}`, `j ≥ 2`, `k > 0`, nonempty
hyperedges, rank at most `d`).

**Formalization Note** `Q` is a `Finset`, so its sets are distinct; "F_h ∪ Q is almost sparse" is
`NoFlowerAtLeast (layer F h ∪ Q) h (2·t_p)`. -/
theorem lemma_B_5 (d j n k h : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hk : 0 < k)
    (F : Finset (Finset (Fin n))) (hrank : ∀ S ∈ F, S.card ≤ d) (hne : ∀ S ∈ F, S.Nonempty)
    (hred : IsReduced F) (hh₁ : 1 ≤ h) (hh : h ≤ tau d j F)
    (Q : Finset (Finset (Fin n))) (hQ : ∀ S ∈ Q, S.card = h)
    (hQF : ∀ S ∈ F, ∀ T ∈ Q, ¬ S ⊆ T)
    (has : NoFlowerAtLeast (layer F h ∪ Q) h (fun p => 2 * tp d j p)) :
    mu d j k (reduceFam (F ∪ Q)) ≤ mu d j k F - ws d j h / 2 * Q.card := by sorry

end RevRedSAT
