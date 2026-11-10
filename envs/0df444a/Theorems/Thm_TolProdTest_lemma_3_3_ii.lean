-- Prove2me | Theorems.Thm_TolProdTest_lemma_3_3_ii
-- name    : TolProdTest.lemma_3_3_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:30.354464+00:00
-- url     : https://prove2.me/theorems/7c7876c1-450a-48d2-8c99-888d76553298
-- title:
--   Lemma 3.3 (ii) — refinement loss: (29) and $Z_{2,C}-Z_2\ge(F_C^2-F_{\mathrm{prod}}^2)/3$
-- statement:
--   Let $n\ge1$, $d\ge2$, $\rho$ a density operator on $(\mathbb C^d)^{\otimes n}$, and $C$ a coloring of the sites into a finite set of colours.
--
--   1. For every family of unit block vectors $|x_c\rangle\in\mathcal H_c$ whose product $|x_C\rangle=\bigotimes_c|x_c\rangle$ attains $F_C(\rho)$, and every nonempty block $B_c$,
--   $$
--   \mathrm{Tr}\big(\Lambda_{C,c}\,\rho^{\otimes 2}\big)\ \ge\ \frac{F_C(\rho)^2}{3}\big(1-F_{\mathrm{prod}}(x_c)^2\big).
--   $$
--   2. $$Z_{2,C}(\rho)-Z_2(\rho)\ \ge\ \frac{F_C(\rho)^2-F_{\mathrm{prod}}(\rho)^2}{3}.$$
--
--   Here $F_{\mathrm{prod}}(x_c)$ is the product fidelity of $|x_c\rangle\langle x_c|$ over the sites of $B_c$. Combined with part (i) this gives Theorem 3.1.
--
--   Differences from the source:
--   - generalization: a coloring C : [n] → [q] → C : Fin n → ι for any finite colour type ι; reason: the proof of (30) applies the one-colour bound (45) to refined colorings with more than q colours (p.13); ι = Fin q is the printed statement
--   - encoding: |x_C⟩ any optimizer achieving F_C(ρ) → any family of unit block vectors x with Re⟨⊗x_c|ρ|⊗x_c⟩ = fC C ρ (a hypothesis of clause 1); reason: the same optimizers; attainment is not assumed elsewhere
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_C(ρ) a maximum over unit block vectors (22); F_q(ρ) a minimum over C : [n] → [q] (23) → fC C ρ the supremum over unit families v_c on the block spaces of Re⟨⊗_c v_c|ρ|⊗_c v_c⟩; fq q ρ = ⨅ over C : Fin n → Fin q (0-based colours); reason: the supremum is attained; a finite infimum over a nonempty finite set is the minimum; an empty block has a one-point basis, i.e. H_c = ℂ as on p.9
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
--   - encoding: Λ_{C,c} (26), Z_{2,C}(ρ) = Tr(Q_{2,C} ρ^{⊗2}), Tr(Λ_{C,c} ρ^{⊗2}) → lambdaCc d C c, zkC C ρ 2, Re Tr(lambdaCc d C c * tensorPow ρ 2): products and differences of averages of register permutations on the basis Fin 2 → Fin n → Fin d; reason: (1/2)(I + SWAP) on a block is its two-copy symmetric projector; the traces are real for ρ ≥ 0
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.3 (ii), eqs. (29)–(30), p.10

import Mathlib
import Definitions.Def_TolProdTest_fC
import Definitions.Def_TolProdTest_zk
import Definitions.Def_TolProdTest_lambdaCc
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Lemma 3.3 (ii) (refinement loss)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.10: "(ii) For any coloring C, let |x_C⟩ = ⊗_c |x_c⟩ be any optimizer
achieving F_C(ρ). Then, for every nonempty block B_c, Tr(Λ_{C,c} ρ^{⊗2}) ≥ (F_C(ρ)²/3)(1 − F_prod(x_c)²). (29)
Moreover, Z_{2,C}(ρ) − Z_2(ρ) ≥ (F_C(ρ)² − F_prod(ρ)²)/3. (30)"

**Formalization Note** The coloring is any `C : Fin n → ι` into a finite colour type (the proof of (30) applies the
one-colour bound to refined colorings with more than `q` colours, p.13). An optimizer is a family of unit vectors
`x_c ∈ H_c` whose block product attains `F_C(ρ)`; `F_prod(x_c)` is the product fidelity of `|x_c⟩⟨x_c|` over the
sites of `B_c`. (30) does not depend on the optimizer. Standing assumptions: `n ≥ 1`, `d ≥ 2`, `ρ` a density
operator. -/
theorem lemma_3_3_ii {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Fin n → ι) (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    (∀ x : ∀ c : ι, ({i // C i = c} → Fin d) → ℂ, (∀ c, IsUnitVec (x c)) →
        (star (blockProd C x) ⬝ᵥ (ρ *ᵥ blockProd C x)).re = fC C ρ →
        ∀ c : ι, (∃ i, C i = c) →
          fC C ρ ^ 2 / 3 * (1 - fprod (Matrix.vecMulVec (x c) (star (x c))) ^ 2) ≤
            (lambdaCc d C c * ShadowTomography.UpperBound.tensorPow ρ 2).trace.re) ∧
    (fC C ρ ^ 2 - fprod ρ ^ 2) / 3 ≤ zkC C ρ 2 - zk ρ 2 := by sorry

end TolProdTest
