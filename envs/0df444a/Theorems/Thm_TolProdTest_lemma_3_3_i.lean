-- Prove2me | Theorems.Thm_TolProdTest_lemma_3_3_i
-- name    : TolProdTest.lemma_3_3_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:16.244145+00:00
-- url     : https://prove2.me/theorems/89d1a385-7725-46bd-89aa-10045fa3ae3e
-- title:
--   Lemma 3.3 (i) — random coloring: $\mathbb E_C\sum_c\Lambda_{C,c}\le I/q$ and $\mathbb E_C[Q_{2,C}-Q_2]\le I/q$
-- statement:
--   Let $n\ge1$, $d\ge2$ and $q\ge13$. Let $C:[n]\to[q]$ be a uniformly random coloring (each register gets an independent uniform colour) and $\Lambda_{C,c}$ the operators of (26) on two copies of $(\mathbb C^d)^{\otimes n}$. Then, in the Loewner order,
--
--   1. $$\mathbb E_C\sum_{c=1}^q\Lambda_{C,c}\ \le\ \frac Iq ,$$
--   2. $$\mathbb E_C\big[Q_{2,C}-Q_2\big]\ \le\ \frac Iq .$$
--
--   This operator bound says that on average over colorings, the two-copy test loses little acceptance when blocks are refined into registers; it yields the random-coloring bound of Theorem 3.1. The threshold $13$ is exactly where the counting estimate (37) starts to hold.
--
--   Differences from the source:
--   - encoding: E_C over an independent uniformly random colour per register → (q^n)^{-1} Σ_{C : Fin n → Fin q}; reason: the uniform distribution on the q^n colorings
--   - encoding: A ≤ B for Hermitian operators → (B − A).PosSemidef; reason: the paper's definition of ≤ (p.8)
--   - encoding: Λ_{C,c}, Q_{2,C}, Q_2 as products of symmetric projectors → lambdaCc, symProjBlocks, qk: averages of register permutations on the basis Fin 2 → Fin n → Fin d; reason: (1/2)(I + SWAP) is the two-copy symmetric projector; same operators
--   - encoding: 'for any mixed state ρ' in the lemma's preamble → no ρ in part (i); reason: (27) and (28) are operator inequalities that do not involve ρ
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.3 (i), eqs. (26)–(28), p.10

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_lambdaCc

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TolProdTest

/-- **Lemma 3.3 (i) (random coloring, operator bound)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.10: "(i) If q ≥ 13 and C assigns each register an
independent uniformly random color, then E_C Σ_{c=1}^q Λ_{C,c} ≤ I/q. (27) Consequently, E_C[Q_{2,C} − Q_2] ≤ I/q.
(28)"

**Formalization Note** `E_C` is the average `q^{−n} Σ_C` over all `q^n` colorings `C : Fin n → Fin q`; `≤` is the
Loewner order (`B − A` positive semidefinite). The operators act on the two-copy space with basis
`Fin 2 → Fin n → Fin d`. `Q_{2,C} = symProjBlocks d C 2`, `Q_2 = qk (Fin n) d 2`, `Λ_{C,c} = lambdaCc d C c`
(26). Standing assumptions: `n ≥ 1`, `d ≥ 2`. -/
theorem lemma_3_3_i {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (q : ℕ) (hq : 13 ≤ q) :
    ((q : ℂ)⁻¹ • (1 : Matrix (Fin 2 → Config n d) (Fin 2 → Config n d) ℂ) -
        ((q : ℂ) ^ n)⁻¹ • ∑ C : Fin n → Fin q, ∑ c : Fin q, lambdaCc d C c).PosSemidef ∧
    ((q : ℂ)⁻¹ • (1 : Matrix (Fin 2 → Config n d) (Fin 2 → Config n d) ℂ) -
        ((q : ℂ) ^ n)⁻¹ • ∑ C : Fin n → Fin q, (symProjBlocks d C 2 - qk (Fin n) d 2)).PosSemidef := by sorry

end TolProdTest
