-- Prove2me | Theorems.Thm_QCopyMono_truncation
-- name    : QCopyMono.truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:48.836804+00:00
-- url     : https://prove2.me/theorems/fbfd87d0-3016-4c6f-8f6b-f498658f144c
-- title:
--   Proof of Lemma 6, p.35 — the truncation $\tilde f$: same $p_t$, still far, and $I[\tilde f]\le I[f]+8\sqrt n$ (eq. (53))
-- statement:
--   Let $n\ge1$, $0<\varepsilon\le1/2$, let $\mathcal B$ be the Hamming band of half-width $w=\lceil\sqrt{(n/2)\log(100/\varepsilon)}\rceil$, and let $\tilde f$ agree with $f$ on $\mathcal B$, equal $0$ below the band and $1$ above it. Then:
--
--   1. every violation of $\tilde f$ (a pair $x\preceq y$ with $\tilde f(x)=1$, $\tilde f(y)=0$) lies entirely within $\mathcal B$ and is a violation of $f$;
--   2. $p_t(f)=p_t(\tilde f)$ for every $t\ge1$;
--   3. $\Pr_x[x\notin\mathcal B]\le 2\exp(-2w^2/n)\le\varepsilon/50$, and $\mathrm{dist}(f,\tilde f)\le\varepsilon/50$;
--   4. if $f$ is $\varepsilon$-far from monotone, then $\tilde f$ is $\tfrac{49}{50}\varepsilon$-far, hence $\tfrac\varepsilon2$-far;
--   5. $I[\tilde f]\le I[f]+8\sqrt n$, and $I[\tilde f]\le 10\sqrt n$ whenever $I[f]\le2\sqrt n$ (eq. (53)).
--
--   These facts let the proof of Lemma 6 replace $f$ by a function whose violations all lie in the middle layers.
--
--   Differences from the source:
--   - generalization: stated in the proof for the ε-far f with I[f] ≤ 2√n of Lemma 6 → clauses 1–3 and the first part of 5 for every f; ε-farness and I[f] ≤ 2√n are hypotheses only of clause 4 and of the second part of 5; reason: the arguments for those clauses do not use the two assumptions; at the lemma's f the statement is the printed one
--   - generalization: n ≥ n_0 (the standing range of Lemma 6) → every n ≥ 1; reason: no clause uses n ≥ n_0 (Hoeffding's bound, the count of band-boundary edges and the truncation argument hold for every n ≥ 1); the lemma's range is an instance
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), proof of Lemma 6 (Appendix A.1), p.35, including eq. (53)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Influence
import Definitions.Def_QCopyMono_PathExperiment

namespace QCopyMono

open QAlgorithms

open Classical in
/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), proof of Lemma 6, p.35, including eq. (53):
the truncation `f̃` of `f` to the band `𝓑` (`f̃ = f` on `𝓑`, `0` below, `1` above). For
`n ≥ 1` and `0 < ε ≤ 1/2`:

1. every violation `x ⪯ y`, `f̃(x) = 1`, `f̃(y) = 0` of `f̃` lies in `𝓑` and is a violation of `f`;
2. `p_t(f) = p_t(f̃)` for every `t ≥ 1`;
3. `Pr_x[x ∉ 𝓑] ≤ 2 exp(−2w²/n) ≤ ε/50`, and `f̃` differs from `f` on at most an `ε/50`
   fraction of inputs;
4. if `f` is `ε`-far from monotone, `f̃` is `49ε/50`-far and `ε/2`-far;
5. `I[f̃] ≤ I[f] + 8√n`, and `I[f̃] ≤ 10√n` when `I[f] ≤ 2√n` (eq. (53)). -/
theorem truncation (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (f : Qubits n → Bool) :
    (∀ x y : Qubits n, x ≤ y → truncate ε f x = true → truncate ε f y = false →
      InBand ε x ∧ InBand ε y ∧ f x = true ∧ f y = false) ∧
    (∀ t : ℕ, 1 ≤ t → pathProb ε t f = pathProb ε t (truncate ε f)) ∧
    ((Finset.univ.filter fun x : Qubits n => ¬ InBand ε x).card : ℝ) / 2 ^ n ≤
      2 * Real.exp (-2 * (bandW ε n : ℝ) ^ 2 / n) ∧
    2 * Real.exp (-2 * (bandW ε n : ℝ) ^ 2 / n) ≤ ε / 50 ∧
    relDist f (truncate ε f) ≤ ε / 50 ∧
    (IsFar ε f → IsFar (49 * ε / 50) (truncate ε f) ∧ IsFar (ε / 2) (truncate ε f)) ∧
    influence (truncate ε f) ≤ influence f + 8 * Real.sqrt n ∧
    (influence f ≤ 2 * Real.sqrt n → influence (truncate ε f) ≤ 10 * Real.sqrt n) := by sorry

end QCopyMono
