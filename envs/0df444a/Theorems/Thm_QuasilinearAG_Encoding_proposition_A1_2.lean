-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_proposition_A1_2
-- name    : QuasilinearAG.Encoding.proposition_A1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:58.57998+00:00
-- url     : https://prove2.me/theorems/1a87a9c9-20d6-4f74-801b-9a6c95fd3939
-- title:
--   Proposition A1.2 — the exceptional groups $S_{l,h}$: $\deg S_{l,h}=(q-1)q^{\min(l,h-l)}$, ramification $e_l=q^{\max(h-2l,0)}$ and the coordinate valuations
-- statement:
--   In the height-$h$ second Garcia–Stichtenoth tower over $k=\mathbb F_{q^2}$ ($q=p^s>2$, $h\ge1$), let $C=\ker(X^q+X)\subset k$ and let $S_{l,h}$ be the reduced divisor of the places with residues $x_0=\dots=x_{l-1}=0$ and $x_l=\alpha\in C^*$. For $0\le l<h$ put $e_l=q^{\max(h-2l,0)}$. Then
--   $$\deg S_{l,h}=(q-1)q^{\min(l,h-l)}.\qquad(A1.7)$$
--   At a place in this group the ramification index over its base place of $k(x_0)$ is $e_l$. For $l\ge1$ the valuations are
--   $$\operatorname{ord}x_i=q^ie_l\ (i<l),\quad \operatorname{ord}x_l=0,\quad \operatorname{ord}(1+x_l^{q-1})=q^le_l,\quad \operatorname{ord}x_i=-q^{\max(h,2l)-i}\ (l<i\le h).\qquad(A1.8)$$
--   For $l=0$ the last pole formula holds and the base ramification index is $q^h$.
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: the reduced divisor S_{l,h} and its degree → the set of places with ord x_i > 0 (i < l) and ord(x_l − α) > 0 for some α ≠ 0 with α^q + α = 0; the set is finite and Σ_P deg P is its degree; reason: a reduced divisor is the sum of its places; residue x_i = 0 means ord x_i > 0
--   - encoding: q^{max(h−2l,0)}; "i > l" → q^(h − 2l) with truncated subtraction; l < i ≤ h; reason: truncated subtraction is max(·, 0); x_i exists only for i ≤ h
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 45, Proposition A1.2, (A1.7)–(A1.8) (PDF p. 47)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-- Proposition A1.2 (All group degrees and coordinate valuations), p. 45 (PDF 47). In the
height-`h` second Garcia–Stichtenoth tower over `k = F_{q²}` (`q > 2` a prime power), let
`0 ≤ l < h`, `e_l = q^{max(h - 2l, 0)}`, and let `S_{l,h}` be the reduced divisor of the places with
residues `x₀ = ⋯ = x_{l-1} = 0`, `x_l = α ∈ C^*` (`C = ker(X^q + X)`). Then
`deg S_{l,h} = (q - 1) q^{min(l, h - l)}` (A1.7); at every place of the group the ramification
index over its base place of `k(x₀)` is `e_l`; for `l ≥ 1` the valuations are
`ord x_i = q^i e_l` (`i < l`), `ord x_l = 0`, `ord(1 + x_l^{q-1}) = q^l e_l`,
`ord x_i = -q^{max(h, 2l) - i}` (`l < i ≤ h`) (A1.8); for `l = 0` the last pole formula holds and
the base ramification index is `q^h`. -/
theorem proposition_A1_2 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (q h : ℕ) (hq : IsPrimePow q) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2) (hh : 1 ≤ h)
    (x : ℕ → F) (hx : IsGSTower k q h x) (l : ℕ) (hl : l < h) :
    (exceptionalGroup (k := k) q x l).Finite ∧
      (∑ᶠ (P : Place k F) (_ : P ∈ exceptionalGroup (k := k) q x l), (P.deg : ℤ)) =
        ((q : ℤ) - 1) * (q : ℤ) ^ min l (h - l) ∧
      (∀ P ∈ exceptionalGroup (k := k) q x l, P.ramIdx (baseField x) = q ^ (h - 2 * l)) ∧
      (1 ≤ l → ∀ P ∈ exceptionalGroup (k := k) q x l,
        (∀ i < l, P.v (x i) = (((q ^ i * q ^ (h - 2 * l) : ℕ) : ℤ) : WithTop ℤ)) ∧
        P.v (x l) = 0 ∧
        P.v (1 + x l ^ (q - 1)) = (((q ^ l * q ^ (h - 2 * l) : ℕ) : ℤ) : WithTop ℤ) ∧
        ∀ i, l < i → i ≤ h →
          P.v (x i) = ((-((q ^ (max h (2 * l) - i) : ℕ) : ℤ) : ℤ) : WithTop ℤ)) ∧
      (l = 0 → ∀ P ∈ exceptionalGroup (k := k) q x l,
        (∀ i, 0 < i → i ≤ h → P.v (x i) = ((-((q ^ (h - i) : ℕ) : ℤ) : ℤ) : WithTop ℤ)) ∧
        P.ramIdx (baseField x) = q ^ h) := by sorry

end QuasilinearAG.Encoding
