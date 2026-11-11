-- Prove2me | Theorems.Thm_PelagicFF_lemma_3_1
-- name    : PelagicFF.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:14.846197+00:00
-- url     : https://prove2.me/theorems/75fc3205-5eaa-4954-8a4b-d28a9b53d99a
-- title:
--   Lemma 3.1 — coupling with the uniform law, $\mathbb E\|W-U\|_2^2\le4\sqrt{s(s-H(W))}$
-- statement:
--   For every random variable $W$ over $\{-1,1\}^s$ there is a coupling $(W,U)$ of $W$ with $U\sim\mathrm{Unif}(\{-1,1\}^s)$ such that
--   $$\mathbb E\|W-U\|_2^2\ \le\ 4\sqrt{s\,(s-H(W))}.$$
--
--   This is a Boolean-cube form of Marton's transportation inequality; Lemma 3.3 and Lemma 4.3 build on it.
--
--   **Formalization Note** A coupling is a law on pairs whose marginals are the law of $W$ and the uniform law; $H$ is in bits.
--
--   Differences from the source:
--   - encoding: random variables on {−1,1}^s → laws (PMF) on ι → Bool for a finite coordinate type ι with s = card ι, bit b read as sign b; reason: relabelling coordinates and values changes no instance
--   - encoding: a coupling (W, U) → a PMF π on pairs with π.map Prod.fst = law of W and π.map Prod.snd = uniform; reason: Definition 2.3, p.16; same couplings
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.1, p.18

import Mathlib
import Definitions.Def_PelagicFF_minEntropyDeficiency
import Definitions.Def_PelagicFF_sqDist

namespace PelagicFF

/-- **Lemma 3.1.** For every random variable `W` over `{−1,1}^s` there is a coupling `(W, U)` of `W`
with `U ∼ Unif({−1,1}^s)` such that `E‖W − U‖₂² ≤ 4√(s(s − H(W)))`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.1, p.18.

**Formalization Note.** `{−1,1}^s` is `ι → Bool` with `s = card ι`; the coupling is a law `π` on
pairs whose first marginal is the law `μ` of `W` and whose second marginal is uniform; `H` is in
bits; `‖W − U‖₂²` is `sqDist`. -/
theorem lemma_3_1 {ι : Type} [Fintype ι] [DecidableEq ι] (μ : PMF (ι → Bool)) :
    ∃ π : PMF ((ι → Bool) × (ι → Bool)),
      π.map Prod.fst = μ ∧ π.map Prod.snd = PMF.uniformOfFintype (ι → Bool) ∧
      ∑ p, (π p).toReal * sqDist p.1 p.2 ≤
        4 * Real.sqrt (Fintype.card ι * (Fintype.card ι - lawEntropy μ)) := by sorry

end PelagicFF
