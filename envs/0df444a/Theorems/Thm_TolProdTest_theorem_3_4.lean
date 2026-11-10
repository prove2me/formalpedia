-- Prove2me | Theorems.Thm_TolProdTest_theorem_3_4
-- name    : TolProdTest.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:33.809435+00:00
-- url     : https://prove2.me/theorems/9b7ddf22-7792-4ce7-b095-e4508c1f4a0b
-- title:
--   Theorem 3.4 — blockwise spectral projection: $Z_k^{1/k}\le\dim\mathrm{Sym}^k(\mathbb C^R)^{q/k}F_q+\frac qR\dim\mathrm{Sym}^k(\mathbb C^R)^{1/k}$
-- statement:
--   Let $n\ge1$, $d\ge2$, $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$, and integers $q,k\ge1$, $R\ge2$. Then
--
--   $$
--   Z_k(\rho)^{1/k}\ \le\ \dim\mathrm{Sym}^k(\mathbb C^R)^{q/k}\,F_q(\rho)+\frac qR\,\dim\mathrm{Sym}^k(\mathbb C^R)^{1/k},
--   \qquad \dim\mathrm{Sym}^k(\mathbb C^R)=\binom{k+R-1}{k}.
--   $$
--
--   The acceptance probability of the $k$-copy test is controlled by the $q$-block fidelity up to a finite-rank factor and a discarded-weight term.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
--   - encoding: dim Sym^k(ℂ^R) → Nat.choose (k + R - 1) k; reason: the paper's own formula, stated with (47), p.13
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 3.4, eq. (47), p.13

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_TolProdTest_zk
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Theorem 3.4 (blockwise spectral projection)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.13: "Let n ≥ 1, d ≥ 2, and ρ ∈ D((C^d)^{⊗n}). For
integers q, k ≥ 1 and R ≥ 2, Z_k(ρ)^{1/k} ≤ dim Sym^k(C^R)^{q/k} F_q(ρ) + (q/R) dim Sym^k(C^R)^{1/k}, (47) where
dim Sym^k(C^R) = (k+R−1 choose k)." -/
theorem theorem_3_4 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (ρ : Matrix (Config n d) (Config n d) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (q k R : ℕ) (hq : 1 ≤ q) (hk1 : 1 ≤ k) (hR : 2 ≤ R) :
    zk ρ k ^ ((1 : ℝ) / k) ≤
      (Nat.choose (k + R - 1) k : ℝ) ^ ((q : ℝ) / k) * fq q ρ +
        (q : ℝ) / R * (Nat.choose (k + R - 1) k : ℝ) ^ ((1 : ℝ) / k) := by sorry

end TolProdTest
