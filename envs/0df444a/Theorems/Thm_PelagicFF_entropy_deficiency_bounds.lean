-- Prove2me | Theorems.Thm_PelagicFF_entropy_deficiency_bounds
-- name    : PelagicFF.entropy_deficiency_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:53.170227+00:00
-- url     : https://prove2.me/theorems/3d2eafad-76b7-4724-8d98-eff127425210
-- title:
--   §2.3, p.16 — $0\le s-H(X)\le D_\infty(X)\le s$
-- statement:
--   For every random variable $X$ on $\{-1,1\}^s$,
--   $$0\ \le\ s-H(X)\ \le\ D_\infty(X)\ \le\ s,$$
--   with $H$ the entropy in bits and $D_\infty$ the min-entropy deficiency (Definition 2.2).
--
--   The middle inequality ($H\ge H_\infty$) is what converts the deficiency hypotheses of Lemma 4.3 into the entropy bound of Lemma 3.1.
--
--   **Formalization Note** Laws on `ι → Bool`, $s=|\iota|$.
--
--   Differences from the source:
--   - encoding: random variables on {−1,1}^s → laws (PMF) on ι → Bool for a finite coordinate type ι with s = card ι, bit b read as sign b; reason: relabelling coordinates and values changes no instance
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.3, p.16

import Mathlib
import Definitions.Def_PelagicFF_minEntropyDeficiency

namespace PelagicFF

/-- **Entropy versus min-entropy deficiency (§2.3, p.16).** For every random variable `X` on
`{−1,1}^s`, `0 ≤ s − H(X) ≤ D∞(X) ≤ s`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.3, p.16, after Definition 2.2: "In particular,
0 ≤ s − H(X) ≤ D∞(X) ≤ s."

**Formalization Note.** `{−1,1}^s` is `ι → Bool` with `s = card ι`; `H` is in bits. -/
theorem entropy_deficiency_bounds {ι : Type} [Fintype ι] [DecidableEq ι] (μ : PMF (ι → Bool)) :
    0 ≤ (Fintype.card ι : ℝ) - lawEntropy μ ∧
    (Fintype.card ι : ℝ) - lawEntropy μ ≤ minEntropyDeficiency μ ∧
    minEntropyDeficiency μ ≤ Fintype.card ι := by sorry

end PelagicFF
