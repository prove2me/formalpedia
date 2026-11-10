-- Prove2me | Theorems.Thm_TolProdTest_fact_3_1
-- name    : TolProdTest.fact_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:23.614871+00:00
-- url     : https://prove2.me/theorems/45c3779f-8a9c-40a9-8669-91c5320a5f59
-- title:
--   Fact 3.1 — $F_{\mathrm{prod}}\le F_q\le F_C$
-- statement:
--   Let $n\ge1$, $d\ge2$, $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$ and $q\in\mathbb N$. For every coloring $C$ of the $n$ sites with at most $q$ nonempty blocks,
--
--   $$
--   F_{\mathrm{prod}}(\rho)\ \le\ F_q(\rho)\ \le\ F_C(\rho).
--   $$
--
--   Every fully product vector is admissible in $F_C$, which gives the first inequality; the second holds because $C$ is one of the colorings over which $F_q$ minimizes.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - reading: a coloring C with at most q nonempty blocks → C : Fin n → ι for any finite colour type ι with |image C| ≤ q; reason: the paper does not fix the codomain; relabelling the nonempty blocks into Fin q leaves F_C unchanged, and ι = Fin q is the case of (23)
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Fact 3.1, p.9

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Fact 3.1**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.9: "For every coloring C with at most q nonempty blocks, F_prod(ρ) ≤ F_q(ρ) ≤ F_C(ρ)."

**Formalization Note** A coloring is any map `C : Fin n → ι` into a finite colour type; "at most `q` nonempty
blocks" is `#(image C) ≤ q`. `F_q` minimizes over `C : Fin n → Fin q` (23). Standing assumptions (§1, p.2):
`n ≥ 1`, `d ≥ 2`, `ρ` a density operator. -/
theorem fact_3_1 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (q : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Fin n → ι) (hC : (Finset.univ.image C).card ≤ q)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    fprod ρ ≤ fq q ρ ∧ fq q ρ ≤ fC C ρ := by sorry

end TolProdTest
