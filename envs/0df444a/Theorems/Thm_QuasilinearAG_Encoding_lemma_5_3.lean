-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_lemma_5_3
-- name    : QuasilinearAG.Encoding.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:42:48.4415+00:00
-- url     : https://prove2.me/theorems/eed4e220-a01e-482a-96aa-9663b0e4e43e
-- title:
--   Lemma 5.3 — the intermediate field: $\deg B_0^E=h(q-1)D-q^h+1$, different exponents $2(e_P-1)$, and $g_E=qD-eq^{\lfloor h/2\rfloor}-q^{\lceil h/2\rceil}+1<qD$
-- statement:
--   In the setting of Lemma 5.2 ($q=p^s>2$, $e=p^r$, $V\subset C$ with $|V|=q/e$, $E=F_{h-1}(z)$, $D=eq^{h-1}$), let $B_0^E$ be the least common effective finite pole divisor of the monomials $m_{a,j}$ of (5.4). Then
--   $$\deg B_0^E=h(q-1)D-q^h+1,\qquad -\operatorname{ord}_{P_\infty}m_{a,j}\le D-1.\qquad(5.5)$$
--   Every finite different exponent of $E/k(x_0)$ is $2(e_P-1)$, where $e_P$ is the ramification index, and infinity has exponent $2(D-1)$. Consequently
--   $$\sum_{P\text{ finite}}(e_P-1)\deg P=g_E,\qquad g_E=qD-eq^{\lfloor h/2\rfloor}-q^{\lceil h/2\rceil}+1<qD.\qquad(5.6)$$
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: an F_p-subspace V ⊂ C of size q/e, e ∈ {p, …, q} → an additive subgroup V of k contained in {v : v^q + v = 0} with Nat.card V = q/e, e = p^r, 1 ≤ r ≤ s; reason: in characteristic p additive subgroups are exactly the F_p-subspaces
--   - encoding: different exponent of P over k(x_0) → HasDifferentExp: ord_P(Dρ) = ord_P(Dπ) + d for D = d/dx_0, π a uniformizer at P, ρ ∈ k(x_0) a uniformizer of the place below; reason: the classical formula d(P|p) = ord_P(dρ/dπ) for a separable extension
--   - encoding: g_E → genus k E = max over divisors A of finite support of deg A − ℓ(A) + 1 (sSup in ℤ); reason: Riemann's definition of the genus
--   - encoding: B_0^E, the sum over finite places, ⌊h/2⌋, ⌈h/2⌉ → finitePoleDivisor (with finite support asserted); a finsum over the places with ord x_0 ≥ 0, with finiteness of the ramified ones asserted; h/2 and (h+1)/2 in ℕ; reason: Lean representation of the same quantities
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 19, Lemma 5.3, (5.5)–(5.6) (PDF p. 21); proof §A1.5, p. 47 (PDF p. 49)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower
import Definitions.Def_QuasilinearAG_Encoding_Intermediate

namespace QuasilinearAG.Encoding

/-- Lemma 5.3 (Exact intermediate pole and different ledger), p. 19 (PDF 21), proved in §A1.5,
p. 47 (PDF 49). In the setting of Lemma 5.2 (`q = p^s > 2`, `e = p^r`, `1 ≤ r ≤ s`, `V ⊂ C` with
`|V| = q/e`, `E = F_{h-1}(z)`, `D = e q^{h-1}`), let `B₀^E` be the least common effective finite pole
divisor of the monomials `m_{a,j}` of (5.4). Then `deg B₀^E = h(q - 1)D - q^h + 1` and
`-ord_{P_∞} m_{a,j} ≤ D - 1` (5.5); every finite different exponent of `E/k(x₀)` is `2(e_P - 1)`,
and infinity has exponent `2(D - 1)`; consequently `Σ_{P finite}(e_P - 1) deg P = g_E` and
`g_E = qD - e q^{⌊h/2⌋} - q^{⌈h/2⌉} + 1 < qD` (5.6). -/
theorem lemma_5_3 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (p s q h : ℕ) [Fact p.Prime] (hqs : q = p ^ s) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2)
    (hh : 1 ≤ h) (x : ℕ → F) (hx : IsGSTower k q h x)
    (r e : ℕ) (hr1 : 1 ≤ r) (hrs : r ≤ s) (he : e = p ^ r)
    (V : AddSubgroup k) (hVC : ∀ v ∈ V, v ^ q + v = 0) (hVcard : Nat.card V = q / e) :
    (Function.support
        (finitePoleDivisor (k := k) (x0InE h x V) (interMono q h e x V))).Finite ∧
      divDeg (finitePoleDivisor (k := k) (x0InE h x V) (interMono q h e x V)) =
        (h : ℤ) * ((q : ℤ) - 1) * ((e : ℤ) * (q : ℤ) ^ (h - 1)) - (q : ℤ) ^ h + 1 ∧
      (∀ P : Place k (interField h x V), P.v (x0InE h x V) < 0 →
        ∀ aj, ((-((e : ℤ) * (q : ℤ) ^ (h - 1) - 1) : ℤ) : WithTop ℤ) ≤
          P.v (interMono q h e x V aj)) ∧
      (∀ P : Place k (interField h x V), 0 ≤ P.v (x0InE h x V) →
        HasDifferentExp P (x0InE h x V)
          (2 * ((P.ramIdx (IntermediateField.adjoin k {x0InE h x V}) : ℤ) - 1))) ∧
      (∀ P : Place k (interField h x V), P.v (x0InE h x V) < 0 →
        HasDifferentExp P (x0InE h x V) (2 * ((e : ℤ) * (q : ℤ) ^ (h - 1) - 1))) ∧
      {P : Place k (interField h x V) | 0 ≤ P.v (x0InE h x V) ∧
        1 < P.ramIdx (IntermediateField.adjoin k {x0InE h x V})}.Finite ∧
      (∑ᶠ (P : Place k (interField h x V)) (_ : 0 ≤ P.v (x0InE h x V)),
          ((P.ramIdx (IntermediateField.adjoin k {x0InE h x V}) : ℤ) - 1) * (P.deg : ℤ)) =
        genus k (interField h x V) ∧
      genus k (interField h x V) =
        (q : ℤ) * ((e : ℤ) * (q : ℤ) ^ (h - 1)) - (e : ℤ) * (q : ℤ) ^ (h / 2)
          - (q : ℤ) ^ ((h + 1) / 2) + 1 ∧
      genus k (interField h x V) < (q : ℤ) * ((e : ℤ) * (q : ℤ) ^ (h - 1)) := by sorry

end QuasilinearAG.Encoding
