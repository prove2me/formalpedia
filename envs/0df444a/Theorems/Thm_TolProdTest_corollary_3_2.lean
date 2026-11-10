-- Prove2me | Theorems.Thm_TolProdTest_corollary_3_2
-- name    : TolProdTest.corollary_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:33.356272+00:00
-- url     : https://prove2.me/theorems/52e6adfd-505b-40e3-a9d1-a4cbf57f04ec
-- title:
--   Corollary 3.2 — $0\le F_q^2-F_{\mathrm{prod}}^2\le\varepsilon_{\mathrm{color}}$
-- statement:
--   Let $n\ge1$, $d\ge2$, $0<\varepsilon_{\mathrm{color}}\le1$ and $q=\max\{13,\lceil3/\varepsilon_{\mathrm{color}}\rceil\}$. For every density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--
--   $$
--   0\ \le\ F_q(\rho)^2-F_{\mathrm{prod}}(\rho)^2\ \le\ \varepsilon_{\mathrm{color}} .
--   $$
--
--   This is the parameter form of Theorem 3.1 used for soundness in Lemma 3.7.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - encoding: ⌈3/ε_color⌉ → ⌈3/ε⌉₊ (Nat.ceil); reason: the argument is positive
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Corollary 3.2, eq. (25), p.10

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Corollary 3.2**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.10: "For any 0 < ε_color ≤ 1, choose q = max{13, ⌈3/ε_color⌉}. Then, for any mixed
state ρ ∈ D((C^d)^{⊗n}), 0 ≤ F_q(ρ)² − F_prod(ρ)² ≤ ε_color. (25)"

Standing assumptions (§1, p.2): `n ≥ 1`, `d ≥ 2`. -/
theorem corollary_3_2 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    0 ≤ fq (max 13 ⌈3 / ε⌉₊) ρ ^ 2 - fprod ρ ^ 2 ∧
      fq (max 13 ⌈3 / ε⌉₊) ρ ^ 2 - fprod ρ ^ 2 ≤ ε := by sorry

end TolProdTest
