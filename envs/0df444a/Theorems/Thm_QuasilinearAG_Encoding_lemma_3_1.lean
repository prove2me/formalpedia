-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_lemma_3_1
-- name    : QuasilinearAG.Encoding.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:49.258207+00:00
-- url     : https://prove2.me/theorems/95937c92-a2b2-4edf-91b4-8b6006e5538b
-- title:
--   Lemma 3.1 — Cartier valuation estimate $\operatorname{ord}_P C_0(f)\ge\lfloor(\operatorname{ord}_P f-(q-1)\delta_P)/q\rfloor$ and its iteration
-- statement:
--   Let $q=p^s>2$, $k=\mathbb F_{q^2}$, and let $F$ be the height-$h$ second Garcia–Stichtenoth tower over $k$ ($h\ge1$), with $t=x_0^q+x_0$ and $C_0$ the zeroth Cartier coefficient of (3.3). For any place $P$ put $\delta_P=\operatorname{ord}_P(dt)-\operatorname{ord}_P(t)$. Then for every nonzero $f\in F$
--   $$\operatorname{ord}_P C_0(f)\ \ge\ \Big\lfloor\frac{\operatorname{ord}_P f-(q-1)\delta_P}{q}\Big\rfloor,\qquad(3.9)$$
--   and for every $j\ge0$
--   $$-\operatorname{ord}_P C_0^j(f)\ \le\ \delta_P+\Big\lceil\frac{-\operatorname{ord}_P f-\delta_P}{q^j}\Big\rceil.\qquad(3.10)$$
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: ord_P(dt) → an integer dtOrd with OrdDiffEq P t dtOrd: ord_P(Dπ) = −dtOrd for the derivation D = d/dt and every uniformizer π; reason: dπ = D(π) dt and ord_P dπ = 0; this is the order of the differential dt
--   - encoding: every f (ord_P f possibly ∞) → f with ord_P f = n ∈ Z, i.e. f ≠ 0; (3.10) as ord_P C_0^j(f) ≥ −(δ_P + ⌈…⌉) in Z ∪ {∞}; reason: for f = 0 both sides are ∞; an ∞ order of C_0^j(f) satisfies (3.10) trivially
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 9, Lemma 3.1, (3.9)–(3.10) (PDF p. 11)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-- Lemma 3.1 (Valuation and iteration), p. 9 (PDF 11). In the height-`h` second
Garcia–Stichtenoth tower `F` over `k = F_{q²}` (`q > 2` a prime power), with `t = x₀^q + x₀` and
`C₀` the zeroth Cartier coefficient of (3.3): for any place `P`, with `δ_P = ord_P(dt) - ord_P(t)`,
every nonzero `f` satisfies `ord_P C₀(f) ≥ ⌊(ord_P f - (q - 1)δ_P)/q⌋` (3.9) and, for every
`j ≥ 0`, `-ord_P C₀^j(f) ≤ δ_P + ⌈(-ord_P f - δ_P)/q^j⌉` (3.10). -/
theorem lemma_3_1 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (q h : ℕ) (hq : IsPrimePow q) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2) (hh : 1 ≤ h)
    (x : ℕ → F) (hx : IsGSTower k q h x)
    (P : Place k F) (dtOrd tOrd : ℤ) (hdt : OrdDiffEq P (towerT q x) dtOrd)
    (ht : P.v (towerT q x) = (tOrd : WithTop ℤ))
    (f : F) (n : ℤ) (hf : P.v f = (n : WithTop ℤ)) :
    ((⌊(((n - ((q : ℤ) - 1) * (dtOrd - tOrd) : ℤ) : ℚ)) / (q : ℚ)⌋ : ℤ) : WithTop ℤ) ≤
        P.v (cartierCoeff q (towerT q x) 0 f) ∧
      ∀ j : ℕ, ((-((dtOrd - tOrd) + ⌈(((-n - (dtOrd - tOrd) : ℤ) : ℚ)) / (q : ℚ) ^ j⌉) : ℤ) :
          WithTop ℤ) ≤ P.v ((cartierCoeff q (towerT q x) 0)^[j] f) := by sorry

end QuasilinearAG.Encoding
