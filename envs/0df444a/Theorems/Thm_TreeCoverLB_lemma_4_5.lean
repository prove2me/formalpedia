-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_4_5
-- name    : TreeCoverLB.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:53.750032+00:00
-- url     : https://prove2.me/theorems/e1b9468e-1358-4d8f-bc89-9ac25204cb4b
-- title:
--   Lemma 4.5: $\|z-\gamma^a z\|_2\ge\sqrt{2/D}\,\tau(z)$ and $|\tau(z)-\tau(z')|\le\sqrt{pD}\,\|z-z'\|_2$
-- statement:
--   Let $p$ be prime, $G=\mathbb Z_p$, $K=E_dG$, $D=d+1$, and let $r\ge 1$ be an integer. For all $z,z'\in C_r$ and every $a\in G\setminus\{0\}$,
--   $$
--   \|z-\gamma^a z\|_2\ \ge\ \sqrt{2/D}\ \tau(z),\qquad |\tau(z)-\tau(z')|\ \le\ \sqrt{pD}\ \|z-z'\|_2 ,
--   $$
--   where $\tau$ is the radial coordinate and $\gamma^a$ the action of $a$.
--
--   These two estimates convert a nonzero winding into Euclidean length in Lemma 4.8.
--
--   Differences from the source:
--   - reading: there are constants δ = δ(d) > 0 and L = L(p, d) > 0 such that …; one may take δ = √(2/D) and L = √(pD) → the two inequalities with δ = √(2/D) and L = √(pD); reason: the lemma's last sentence asserts these values; the existential follows
--   - encoding: the radial coordinate τ(tx) = t → the coordinate sum Σ_v z_v; reason: equal on C_r (proof of Lemma 4.5)
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone

open Classical

namespace TreeCoverLB

/-- **Lemma 4.5** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.5, p.12 (PDF p.14)): let `p` be a prime, `G = ℤ_p`, `K = E_dG`,
`D = d + 1`, `r ≥ 1` an integer, and `γ^a` the action of `a ∈ ℤ_p` on the cone `C_r`. For every
`z, z' ∈ C_r` and every `a ∈ G ∖ {0}`,
`‖z − γ^a z‖₂ ≥ δ τ(z)` and `|τ(z) − τ(z')| ≤ L ‖z − z'‖₂`,
with the constants the lemma names: `δ = √(2/D)` and `L = √(pD)`.

**Formalization Note** `τ` is the coordinate sum (`radial`), equal to the paper's radial coordinate
on `C_r`. The lemma's "there are constants δ = δ(d) > 0 and L = L(p, d) > 0 … One may take
δ = √(2/D) and L = √(pD)" is stated with these explicit values. -/
theorem lemma_4_5 (p : ℕ) [Fact p.Prime] (d r : ℕ) (hr : 1 ≤ r) :
    ∀ z ∈ scaledCone (EJoin d (ZMod p)) r, ∀ z' ∈ scaledCone (EJoin d (ZMod p)) r,
      ∀ a : ZMod p, a ≠ 0 →
        Real.sqrt (2 / ((d : ℝ) + 1)) * radial z ≤ euclid z (ejoinAct a z) ∧
        |radial z - radial z'| ≤ Real.sqrt ((p : ℝ) * ((d : ℝ) + 1)) * euclid z z' := by sorry

end TreeCoverLB
