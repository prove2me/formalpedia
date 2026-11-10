-- Prove2me | Theorems.Thm_TolProdTest_corollary_3_5
-- name    : TolProdTest.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:44.166761+00:00
-- url     : https://prove2.me/theorems/c6e490bf-dca0-464d-a6f6-3ce18c91e20d
-- title:
--   Corollary 3.5 — $Z_k(\rho)^{1/k}\le F_q(\rho)+\varepsilon_{\mathrm{sp}}$ for $k\ge k_{\mathrm{sp}}$
-- statement:
--   Let $n\ge1$, $d\ge2$, $q\ge1$, $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$ and $0<\varepsilon_{\mathrm{sp}}\le1$. Set
--
--   $$
--   R=\Big\lceil\frac{4q}{\varepsilon_{\mathrm{sp}}}\Big\rceil,\qquad
--   k_{\mathrm{sp}}=\Big\lceil\frac{8qR\max\{F_q(\rho),\varepsilon_{\mathrm{sp}}\}}{\varepsilon_{\mathrm{sp}}}\log\Big(\frac{8eq\max\{F_q(\rho),\varepsilon_{\mathrm{sp}}\}}{\varepsilon_{\mathrm{sp}}}\Big)\Big\rceil .
--   $$
--
--   Then for every integer $k\ge k_{\mathrm{sp}}$,
--
--   $$
--   Z_k(\rho)^{1/k}\ \le\ F_q(\rho)+\varepsilon_{\mathrm{sp}} .
--   $$
--
--   This is the parameter form of Theorem 3.4 used for soundness in Lemma 3.7.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
--   - encoding: ceilings and log in (48) → ⌈·⌉₊ (Nat.ceil) and Real.log (natural); reason: arguments are positive; log is natural (p.8)
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Corollary 3.5, eqs. (48)–(49), p.13

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_TolProdTest_zk
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Corollary 3.5 (parameters for blockwise spectral projection)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.13: "Let n, d, q be integers with n ≥ 1,
d ≥ 2, q ≥ 1, and let ρ ∈ D((C^d)^{⊗n}). For 0 < ε_sp ≤ 1, set R := ⌈4q/ε_sp⌉,
k_sp := ⌈(8qR max{F_q(ρ), ε_sp}/ε_sp) log(8eq max{F_q(ρ), ε_sp}/ε_sp)⌉. (48) For every integer k ≥ k_sp,
Z_k(ρ)^{1/k} ≤ F_q(ρ) + ε_sp. (49)"

**Formalization Note** `log` is the natural logarithm; ceilings are `Nat.ceil`. -/
theorem corollary_3_5 {n d q : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (hq : 1 ≤ q)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ)
    (hk : ⌈8 * (q : ℝ) * (⌈4 * (q : ℝ) / ε⌉₊ : ℝ) * max (fq q ρ) ε / ε *
        Real.log (8 * Real.exp 1 * (q : ℝ) * max (fq q ρ) ε / ε)⌉₊ ≤ k) :
    zk ρ k ^ ((1 : ℝ) / k) ≤ fq q ρ + ε := by sorry

end TolProdTest
