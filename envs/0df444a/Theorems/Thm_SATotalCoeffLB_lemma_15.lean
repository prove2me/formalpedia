-- Prove2me | Theorems.Thm_SATotalCoeffLB_lemma_15
-- name    : SATotalCoeffLB.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:08.599701+00:00
-- url     : https://prove2.me/theorems/cc5ea8f2-e471-49e7-9ba7-8c24f7a6930f
-- title:
--   Lemma 15 — locally testable LDPC codes with rate $\ge 1/3$, distance $\ge\delta m$ and $\mathrm{dist}(z,C)\le A\,\mathrm{wt}(Hz)$
-- statement:
--   There are constants $\delta > 0$ and $A, B \ge 1$, an integer $w \ge 1$, and an infinite family of binary linear codes $C \subseteq \mathbb F_2^m$ of dimension at least $m/3$ and minimum distance at least $\delta m$, such that each $C$ has a parity-check matrix $H \in \mathbb F_2^{t\times m}$, i.e. $C = \ker H$, with $t \le Bm$ rows and every column of Hamming weight at most $w$. Furthermore, for every $z \in \mathbb F_2^m$,
--
--   $$
--   \operatorname{dist}(z, C) \le A \operatorname{wt}(Hz), \tag{26}
--   $$
--
--   where $\operatorname{wt}$ is the Hamming weight and $\operatorname{dist}(z, C) = \min_{c\in C} \operatorname{wt}(z + c)$.
--
--   This lemma restates a theorem of Panteleev and Kalachev ([PK22, Theorem 1], asymptotically good locally testable LDPC codes) in the form used for the construction. The matrix $H$ defines the parity checks of the system of Theorem 3; (26) is what makes low-weight preimages under $H$ unique in the proof of Lemma 19.
--
--   **Formalization Note** The family is infinite exactly when its lengths $m$ are unbounded, which is what the statement asserts: for every $M$ there is such a code of length $m \ge M$.
--
--   Differences from the source:
--   - encoding: an infinite family of codes $C \subseteq \mathbb F_2^m$ → for every $M$ a length $m \ge M$ with such a code; reason: each length carries only finitely many codes, so a family is infinite iff its lengths are unbounded
--   - encoding: $\mathrm{dist}(z,C) \le A\,\mathrm{wt}(Hz)$ with $\mathrm{dist}(z,C) = \min_{c\in C}\mathrm{wt}(z+c)$ → some $c$ with $Hc = 0$ has $\mathrm{wt}(z+c) \le A\,\mathrm{wt}(Hz)$; reason: the minimum over the finite nonempty set $C$ is attained
--   - encoding: dimension, minimum distance, $C = \ker H$ → `finrank` of the kernel of $z \mapsto Hz$; every nonzero $z$ with $Hz = 0$ has weight $\ge \delta m$; weights are `hammingNorm`; reason: standard Lean notions; same values
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 15, p.50

import Mathlib

namespace SATotalCoeffLB

/-- **Lemma 15 (the coding ingredient)**, p.50 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

There are constants `δ > 0`, `A, B ≥ 1` and an integer `w ≥ 1` such that for arbitrarily large
lengths `m` there is a parity-check matrix `H ∈ F₂^{t×m}` with `t ≤ Bm` rows and every column of
weight at most `w`, whose code `C = ker H` has dimension at least `m/3` and minimum distance at
least `δm`, and such that `dist(z, C) ≤ A·wt(Hz)` for every `z ∈ F₂^m` (Eq. (26)). The lemma restates
[PK22, Theorem 1] (Panteleev–Kalachev).

**Formalization Note** "An infinite family of codes `C ⊆ F₂^m`" is read as: lengths `m` are
unbounded (each length carries finitely many codes). `wt` is `hammingNorm`; `dist(z, C) =
min_{c ∈ C} wt(z + c)` is expressed by the existence of a codeword `c` with
`wt(z + c) ≤ A·wt(Hz)`. -/
theorem lemma_15 :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ w : ℕ, 1 ≤ w ∧
      ∀ M : ℕ, ∃ m ≥ M, ∃ t : ℕ, ∃ H : Matrix (Fin t) (Fin m) (ZMod 2),
        (t : ℝ) ≤ B * m ∧
        (∀ j : Fin m, hammingNorm (fun i => H i j) ≤ w) ∧
        (m : ℝ) / 3 ≤ (Module.finrank (ZMod 2) (LinearMap.ker H.mulVecLin) : ℝ) ∧
        (∀ z : Fin m → ZMod 2, H.mulVec z = 0 → z ≠ 0 → δ * m ≤ (hammingNorm z : ℝ)) ∧
        ∀ z : Fin m → ZMod 2, ∃ c : Fin m → ZMod 2, H.mulVec c = 0 ∧
          (hammingNorm (z + c) : ℝ) ≤ A * (hammingNorm (H.mulVec z) : ℝ) := by sorry

end SATotalCoeffLB
