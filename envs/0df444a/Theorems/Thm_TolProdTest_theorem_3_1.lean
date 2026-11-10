-- Prove2me | Theorems.Thm_TolProdTest_theorem_3_1
-- name    : TolProdTest.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:29.911719+00:00
-- url     : https://prove2.me/theorems/52d8e8bf-30d7-4baa-b139-908bbcd633ec
-- title:
--   Theorem 3.1 — random coloring: $F_{\mathrm{prod}}^2\le F_q^2\le F_{\mathrm{prod}}^2+3/q$
-- statement:
--   Let $n\ge1$, $d\ge2$, $q\ge13$ an integer and $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$. Then
--
--   $$
--   F_{\mathrm{prod}}(\rho)^2\ \le\ F_q(\rho)^2\ \le\ F_{\mathrm{prod}}(\rho)^2+\frac3q .
--   $$
--
--   Coarse-graining the $n$ registers into $q$ blocks increases the squared optimal product fidelity by at most $3/q$, independently of $n$ and $d$.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 3.1, eq. (24), p.9

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Theorem 3.1 (random coloring)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.9: "Given n ≥ 1, d ≥ 2, for every integer q ≥ 13 and any mixed state
ρ ∈ D((C^d)^{⊗n}), the following inequality holds F_prod(ρ)² ≤ F_q(ρ)² ≤ F_prod(ρ)² + 3/q. (24)" -/
theorem theorem_3_1 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (q : ℕ) (hq : 13 ≤ q)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    fprod ρ ^ 2 ≤ fq q ρ ^ 2 ∧ fq q ρ ^ 2 ≤ fprod ρ ^ 2 + 3 / (q : ℝ) := by sorry

end TolProdTest
