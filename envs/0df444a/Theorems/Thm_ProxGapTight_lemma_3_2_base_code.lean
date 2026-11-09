-- Prove2me | Theorems.Thm_ProxGapTight_lemma_3_2_base_code
-- name    : ProxGapTight.lemma_3_2_base_code
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:52:05.077364+00:00
-- url     : https://prove2.me/theorems/8b17302b-2bb4-4e2b-b6c0-575ec3416c5d
-- title:
--   Lemma 3.2 — the small-distance counterexample $C_m, f_m, g_m$
-- statement:
--   Fix a prime $p$ and $Q=p^a>32$ with $Q\notin\{49,121\}$. There is a constant $c_Q>0$, depending only on $Q$, such that for all sufficiently large $m$, with $q_m=Q^{2m}$,
--   $$
--   n_m=\frac{Q^m-1}{Q-1},\qquad e_m=\frac{Q^{m-2}-1}{Q-1},\qquad L_m=3Q^{m-3}-3Q^{m-4}-1,
--   $$
--   there are a linear code $C_m\subseteq\mathbb F_{q_m}^{n_m}$ and vectors $f_m,g_m\in\mathbb F_{q_m}^{n_m}$ with
--
--   1. **Code parameters.** $\dfrac{L_m}{n_m}<\delta(C_m)<\dfrac{3e_m}{n_m}$;
--   2. **Distance of the defining vectors.** $\delta(f_m,C_m)>\dfrac{4e_m}{3n_m}$ and $\delta(g_m,C_m)>\dfrac{4e_m}{3n_m}$;
--   3. **Exceptional coefficients.** $|\mathcal Z_{e_m/n_m}(f_m,g_m;C_m)|\ge c_Q\,q_m$.
--
--   With $x=e_m/n_m$ this is a code of distance about $3x$, words at distance more than $4x/3$, and a constant fraction of coefficients at radius $x$: the one-and-a-half Johnson regime at small distance, which the proof of Theorem 1.1 amplifies to every distance.
--
--   **Formalization Note** $\mathbb F_{q_m}$ is any field of order $(p^a)^{2m}$, and the code is nonzero.
--
--   Differences from the source:
--   - generalization: F_{q_m} → any field with Fintype.card = (p ^ a) ^ (2 * m); reason: all fields of that order are isomorphic to it; the statement specializes to it
--   - encoding: δ(C_m) for a code the lemma produces → C ≠ ⊥ added to the conclusion; reason: δ(C) presupposes a nonzero code; in Lean minDist ⊥ = 0 by the sInf ∅ = 0 convention
--   - encoding: c_Q depending only on Q; for all sufficiently large m → ∃ c_Q > 0 before ∃ m₀ ∀ m ≥ m₀ and before the field; reason: the stated dependency
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.2, p.7 (proof pp.11–12)

import Mathlib
import Definitions.Def_ProxGapTight_relDist
import Definitions.Def_ProxGapTight_distToCode
import Definitions.Def_ProxGapTight_exceptionalSet
import Definitions.Def_ProxGapTight_nm
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm

namespace ProxGapTight

/-- **Lemma 3.2**, Kominers, Thaler, Zheng, manuscript (Sept. 2026), p.7 (proof pp.11–12). Fix a
prime `p` and a power `Q = p^a > 32`, `Q ∉ {49, 121}`. There is `c_Q > 0` depending only on `Q`
such that for all sufficiently large `m`, with `q_m = Q^{2m}`, there are a linear code
`C_m ⊆ F_{q_m}^{n_m}` and `f_m, g_m ∈ F_{q_m}^{n_m}` with `L_m/n_m < δ(C_m) < 3e_m/n_m`,
`δ(f_m, C_m), δ(g_m, C_m) > 4e_m/(3n_m)` and `|𝒵_{e_m/n_m}(f_m, g_m; C_m)| ≥ c_Q q_m`.

**Formalization Note.** `F_{q_m}` is any field `F` of order `(p^a)^{2m}`; the `n_m` coordinates
are `Fin (nm Q m)` (the paper indexes them by the lines of `F_Q^m`; any bijection). `c_Q` is
chosen before `m` and `F`; "sufficiently large `m`" is `∃ m₀`. `C ≠ ⊥` is stated explicitly. -/
theorem lemma_3_2_base_code (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ cQ : ℝ, 0 < cQ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = (p ^ a) ^ (2 * m) →
        ∃ C : Submodule F (Fin (nm (p ^ a) m) → F), ∃ f g : Fin (nm (p ^ a) m) → F,
          C ≠ ⊥ ∧
          (Lm (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) < relDist C ∧
          relDist C < 3 * (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) ∧
          4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) < distToCode f C ∧
          4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) < distToCode g C ∧
          cQ * (((p ^ a) ^ (2 * m) : ℕ) : ℝ) ≤
            ((exceptionalSet ((em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ)) f g C).card : ℝ) := by sorry

end ProxGapTight
