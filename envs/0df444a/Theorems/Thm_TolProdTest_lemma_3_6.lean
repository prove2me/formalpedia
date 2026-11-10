-- Prove2me | Theorems.Thm_TolProdTest_lemma_3_6
-- name    : TolProdTest.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:55.136118+00:00
-- url     : https://prove2.me/theorems/7470e65d-a6f7-4989-867e-94c6f7f4f3fb
-- title:
--   Lemma 3.6 — successive compressions (54) and high/low bounds (55)
-- statement:
--   Let $n\ge1$, $d\ge2$, $C:[n]\to[q]$, $R\ge2$, $k\ge1$, and $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$, with $\omega^{\mathrm{hi}}_q$, $\omega^{\mathrm{lo}}_c$ the compressions of (53). Then:
--
--   1. $$Z_k(\rho)^{1/k}\le Z_{k,C}(\rho)^{1/k}\le Z_{k,C}(\omega^{\mathrm{hi}}_q)^{1/k}+\sum_{c=1}^qZ_{k,C}(\omega^{\mathrm{lo}}_c)^{1/k};$$
--   2. $$Z_{k,C}(\omega^{\mathrm{hi}}_q)^{1/k}\le\dim\mathrm{Sym}^k(\mathbb C^R)^{q/k}F_C(\rho),\qquad Z_{k,C}(\omega^{\mathrm{lo}}_c)^{1/k}\le\frac{\dim\mathrm{Sym}^k(\mathbb C^R)^{1/k}}{R}\quad\forall c\in[q].$$
--
--   The bounded-rank core is controlled by $F_C(\rho)$ and each discarded part by $1/R$; together they give Theorem 3.4.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
--   - encoding: dim Sym^k(ℂ^R) → Nat.choose (k + R - 1) k; reason: the paper's own formula, stated with (47), p.13
--   - encoding: colours c ∈ [q], Π^hi_{<c} = ∏_{j<c} Π^hi_j, ω^hi_q, ω^lo_c → 0-based colours Fin q; omegaHi C R ρ q and omegaLo C R ρ c (product over j < c in the order of Fin q); reason: relabelling 1..q as 0..q−1; the projectors of different colours commute
--   - encoding: Z_{k,C} of the non-normalized positive operators ω → the same trace formula zkC; x^{1/k} the real power of a nonnegative real; reason: as in the paper
--   - encoding: ρ_c = Tr_{−c} ρ and Π^hi_c = 1_{(1/R,1]}(ρ_c) acting on block B_c → blockMarginal C c ρ (entries Σ_z ρ_{(x,z),(y,z)}) and highProj, the continuous functional calculus of the indicator of (1/R, 1], lifted to the whole space as A ⊗ I by liftBlock; reason: the partial trace in the computational basis; for a Hermitian operator cfc of the indicator is the spectral projector Σ_{λ_j ∈ (1/R,1]} |v_j⟩⟨v_j| (any function is continuous on a finite spectrum)
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.6, eqs. (53)–(55), p.14

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_TolProdTest_zk
import Definitions.Def_TolProdTest_omegaHi
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Lemma 3.6 (successive compressions)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.14: "Fix C : [n] → [q], R ≥ 2, k ≥ 1, and ρ ∈ D((C^d)^{⊗n}). For
each c ∈ [q], let ρ_c := Tr_{−c} ρ, Π^hi_c := 1_{(1/R,1]}(ρ_c) be the projector to the eigenspaces of ρ_c with
eigenvalues larger than 1/R, Π^lo_c := I − Π^hi_c, and Π^hi_{<c} := ∏_{j<c} Π^hi_j, with Π^hi_{<1} = I. Set
ω^hi_0 := ρ and ω^hi_c := Π^hi_c Π^hi_{<c} ρ Π^hi_{<c} Π^hi_c, ω^lo_c := Π^lo_c Π^hi_{<c} ρ Π^hi_{<c} Π^lo_c. (53)
Note that ω^hi_q = (⊗_c Π^hi_c) ρ (⊗_c Π^hi_c). Then: (i) The successive compressions satisfy
Z_k(ρ)^{1/k} ≤ Z_{k,C}(ρ)^{1/k} ≤ Z_{k,C}(ω^hi_q)^{1/k} + Σ_{c=1}^q Z_{k,C}(ω^lo_c)^{1/k}. (54) (ii) The high- and
low-eigenspace parts obey Z_{k,C}(ω^hi_q)^{1/k} ≤ dim Sym^k(C^R)^{q/k} F_C(ρ),
Z_{k,C}(ω^lo_c)^{1/k} ≤ dim Sym^k(C^R)^{1/k}/R ∀c ∈ [q]. (55)"

**Formalization Note** Colours are 0-based (`Fin q`); `omegaHi C R ρ q` is `ω^hi_q` and `omegaLo C R ρ c` is
`ω^lo_c`. `Z_{k,C}` of a non-normalized positive operator is the same trace formula. Powers `x^{1/k}` are real
powers of nonnegative reals. `dim Sym^k(ℂ^R) = C(k + R − 1, k)`. Standing assumptions: `n ≥ 1`, `d ≥ 2`. -/
theorem lemma_3_6 {n d q : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (C : Fin n → Fin q) (R k : ℕ) (hR : 2 ≤ R)
    (hk1 : 1 ≤ k) (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    (zk ρ k ^ ((1 : ℝ) / k) ≤ zkC C ρ k ^ ((1 : ℝ) / k) ∧
      zkC C ρ k ^ ((1 : ℝ) / k) ≤
        zkC C (omegaHi C R ρ q) k ^ ((1 : ℝ) / k) +
          ∑ c : Fin q, zkC C (omegaLo C R ρ c) k ^ ((1 : ℝ) / k)) ∧
    (zkC C (omegaHi C R ρ q) k ^ ((1 : ℝ) / k) ≤
        (Nat.choose (k + R - 1) k : ℝ) ^ ((q : ℝ) / k) * fC C ρ ∧
      ∀ c : Fin q, zkC C (omegaLo C R ρ c) k ^ ((1 : ℝ) / k) ≤
        (Nat.choose (k + R - 1) k : ℝ) ^ ((1 : ℝ) / k) / R) := by sorry

end TolProdTest
