-- Prove2me | Theorems.Thm_SecondBestBT_Supplement_theorem_5_13
-- name    : SecondBestBT.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:39:30.738632+00:00
-- url     : https://prove2.me/theorems/a26defb0-bd83-4d6b-9221-f5cfc1c2d5a2
-- title:
--   Theorem 5.13 — a buyer-independent certificate for general discrete sellers
-- statement:
--   Fix $\alpha\ge0$ and a seller prior $F_S$ on $\mathbb Z_{\ge0}$ with masses $f_S$ and $f_S(0)>0$ (infinite support and internal zero masses are allowed). There exists an allocation $x_\alpha\in R_3$, depending only on $(F_S,\alpha)$, such that, with $\beta=\tfrac12$,
--   $$
--   H(b;x_\alpha)\ \ge\ 0\qquad\text{for every } b\in\mathbb Z_{\ge0}.
--   $$
--   Consequently, for every independent buyer prior $F_B$ on $\mathbb Z_{\ge0}$ with finite first-best GFT, the series defining $\mathrm{GFT}(x_\alpha)$ and $\Lambda_D(x_\alpha)$ converge absolutely and
--   $$
--   \mathrm{GFT}(x_\alpha)+\alpha\,\Lambda_D(x_\alpha)\ \ge\ \tfrac12\,\mathrm{FB}.
--   $$
--
--   Here $R_3$ is the class of allocations $x:\mathbb Z_{\ge0}^2\to[0,1]$ that are weakly increasing in the buyer value, weakly decreasing in the seller value and zero when $s\ge b$, and $H(b;x)$ is the buyer-wise residual of Eq. (4). The theorem extends the Lagrangian certificate of Theorem 4.10 from regular full-support sellers to every discrete seller with an atom at $0$, with a single allocation serving every buyer prior.
--
--   Differences from the source:
--   - encoding: a seller (buyer) prior on $\mathbb Z_{\ge0}$ → a mass function $f\ge0$ on $\mathbb N$ with $\sum f=1$ (`HasSum f 1`); reason: a probability distribution on $\mathbb Z_{\ge0}$ is its mass function; same instances
--   - encoding: $x_\alpha$ "depending only on $(F_S,\alpha)$" → $\exists x$ quantified before every buyer prior $f_B$; reason: the quantifier order says exactly that $x$ does not depend on the buyer
--   - encoding: $\mathrm{GFT}$, $\Lambda_D$, $\mathrm{FB}$ for a buyer prior on $\mathbb Z_{\ge0}$ with finite first-best GFT → series over $(s,b)\in\mathbb N\times\mathbb N$ of the published summands `gftTermN`, `lambdaTermN`, `fbTermN`; finite FB is summability of the FB series and the conclusion includes summability of the GFT and $\Lambda_D$ series; reason: as in the published Theorem 4.10; the paper notes the series converges absolutely (p.41), and stating summability rules out the junk value of a divergent series
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 5.13, p.24

import Mathlib
import Definitions.Def_SecondBestBT_R3N
import Definitions.Def_SecondBestBT_H
import Definitions.Def_SecondBestBT_gftTermN
import Definitions.Def_SecondBestBT_lambdaTermN
import Definitions.Def_SecondBestBT_fbTermN

namespace SecondBestBT.Supplement

/-- **Theorem 5.13** (a buyer-independent certificate for general discrete sellers;
Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version
sha256 17184930…, Theorem 5.13, p.24). Fix `α ≥ 0` and a seller prior `F_S` on `ℤ_{≥0}` with
`f_S(0) > 0`. There exists `x_α ∈ R3`, depending only on `(F_S, α)`, such that `H(b; x_α) ≥ 0`
for every `b ∈ ℤ_{≥0}`. Consequently, for every independent buyer prior on `ℤ_{≥0}` with finite
first-best GFT, `GFT(x_α) + α Λ_D(x_α) ≥ ½ FB`.

**Formalization Note** Section 5 fixes `β = 1/2` (p.15), so `H` is the published `SecondBestBT.H`
with `β = 1/2`, evaluated with the original seller masses (p.24). A prior on `ℤ_{≥0}` is a mass
function `f ≥ 0` with `∑ f = 1`; the seller may have infinite support and internal zero masses.
"Depending only on `(F_S, α)`" is the quantifier order: `x` is chosen before the buyer prior. For
a buyer prior with infinite support, `GFT`, `Λ_D` and `FB` are series over `(s, b) ∈ ℕ × ℕ`
(as in the published `SecondBestBT.theorem_4_10`); finite first-best GFT is summability of the
`FB` series, and the conclusion asserts summability of the `GFT` and `Λ_D` series. -/
theorem theorem_5_13 (α : ℝ) (hα : 0 ≤ α) (fS : ℕ → ℝ) (hfS : ∀ s, 0 ≤ fS s)
    (hfS1 : HasSum fS 1) (hfS0 : 0 < fS 0) :
    ∃ x ∈ R3N, (∀ b, 0 ≤ H α (1 / 2) fS x b) ∧
      ∀ fB : ℕ → ℝ, (∀ b, 0 ≤ fB b) → HasSum fB 1 → Summable (fbTermN fS fB) →
        Summable (gftTermN fS fB x) ∧ Summable (lambdaTermN fS fB x) ∧
        1 / 2 * ∑' p, fbTermN fS fB p ≤
          (∑' p, gftTermN fS fB x p) + α * ∑' p, lambdaTermN fS fB x p := by sorry

end SecondBestBT.Supplement
