-- Prove2me | Theorems.Thm_TolProdTest_eq_40
-- name    : TolProdTest.eq_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:20.863454+00:00
-- url     : https://prove2.me/theorems/320d3d34-469c-4a49-b2b1-bdcb483a1c98
-- title:
--   Eq. (40) [BJW26] — pure-state two-copy bound $1-Z_2(v)\ge(1-F_{\mathrm{prod}}(v)^2)/3$
-- statement:
--   Let $S$ be a finite set of sites, each carrying $\mathbb C^d$ with $d\ge2$, and let $|v\rangle$ be a unit vector in $(\mathbb C^d)^{\otimes S}$. Then the two-copy product test satisfies
--
--   $$
--   1-Z_2(v)\ \ge\ \frac{1-F_{\mathrm{prod}}(v)^2}{3},
--   $$
--
--   where $Z_2(v)=\mathrm{Tr}[Q_2(|v\rangle\langle v|)^{\otimes 2}]$ and $F_{\mathrm{prod}}(v)=\max_\pi|\langle\pi|v\rangle|^2$. The paper cites it from Theorem 1.1 of [BJW26] and applies it to the optimal block vectors in the proof of Lemma 3.3 (ii).
--
--   Differences from the source:
--   - reading: every pure multipartite state |v⟩ → every unit vector v on (ℂ^d)^{⊗S}, S any finite set of sites, d ≥ 2; reason: §2.1 fixes H_i = ℂ^d for every register, and (40) is applied to the block spaces H_c = ⊗_{i∈B_c} ℂ^d
--   - encoding: F_prod(v), Z_2(v) of a pure state → fprod and zk of Matrix.vecMulVec v (star v) = |v⟩⟨v|; reason: the identification of p.8
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.3 (ii), eq. (40), p.12 (cited from [BJW26, Theorem 1.1])

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_zk

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Pure-state two-copy product-test bound, eq. (40)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.3 (ii), p.12: "We use the
pure-state two-copy product-test bound 1 − Z_2(v) ≥ (1 − F_prod(v)²)/3 (40) for every pure multipartite state |v⟩;
it follows directly from Theorem 1.1 of [BJW26]."

**Formalization Note** The parties form any finite type `S` (the paper applies (40) to the sites of a
colour block), each of local dimension `d ≥ 2`. A pure state is a unit vector `v`, identified with `|v⟩⟨v|`
(`Matrix.vecMulVec v (star v)`, p.8), so `Z_2(v) = Tr[Q_2 (|v⟩⟨v|)^{⊗2}]` and `F_prod(v) = max_π |⟨π|v⟩|²`. -/
theorem eq_40 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (hd : 2 ≤ d)
    (v : (S → Fin d) → ℂ) (hv : IsUnitVec v) :
    (1 - fprod (Matrix.vecMulVec v (star v)) ^ 2) / 3 ≤ 1 - zk (Matrix.vecMulVec v (star v)) 2 := by sorry

end TolProdTest
