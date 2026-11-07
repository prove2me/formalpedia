-- Prove2me | Theorems.Thm_PNormReg_lemma_7
-- name    : PNormReg.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:18.345549+00:00
-- url     : https://prove2.me/theorems/f638c81d-1de2-4d28-b914-97b5e74bbd12
-- title:
--   Lemma 7, p.19 — iterative refinement: if every call succeeds, Algorithm 2 returns an $\epsilon$-additive solution after $O(p\kappa\log(2+\nu_0/\epsilon))$ calls
-- statement:
--   Run Algorithm 2 on a problem (11) with $p\ge2$, $\kappa\ge1$, $\epsilon>0$, a feasible $x^{(0)}$ and $\nu_0\ge f(x^{(0)})-f^\star$. If every residual call succeeds, that is, returns $\Delta$ with $C\Delta=0$ and with
--
--   $$\mathrm{res}_p(\Delta)\ge\mathrm{res}^\star_p/\kappa\quad\text{whenever }f(x)-f^\star>\nu/2,$$
--
--   then the returned point $x$ is feasible and satisfies $f(x)\le f^\star+\epsilon$, after at most $C\,p\,\kappa\log(2+\nu_0/\epsilon)$ residual calls, with $C$ an absolute constant. The cap $T$ of Algorithm 2 obeys the same bound.
--
--   The lemma reduces high-accuracy regression to a number of constant-accuracy subproblems logarithmic in the initial gap.
--
--   Differences from the source:
--   - encoding: "Algorithm 2" with a residual solver → a run over an arbitrary sequence of returned directions, each free; reason: the lemma only uses the success condition of the calls, so this covers every solver
--   - encoding: O(pκ log(2 + ν₀/ϵ)) → ∃ C > 0 absolute, before all the data; both the call count and the cap T are bounded; reason: the meaning of O(·); the cap T is what makes the loop reach ν ≤ ϵ
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 7, p.19 (PDF p.20); Algorithm 2, p.18

import Mathlib
import Definitions.Def_PNormReg_Refinement

open Matrix

namespace PNormReg

/-- **Lemma 7** (Iterative refinement, adapted from Theorem 2.1 of [AKPS24]), p.19 (PDF p.20).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

"If every residual call (Line 5) in Algorithm 2 succeeds, then it returns an ϵ-additive approximate
solution to (11) after O(pκ log(2 + ν0/ϵ)) residual calls."

There is an absolute `C` such that for all the data and every sequence of solver outputs whose every
call succeeds, the returned `x` is feasible with `f(x) ≤ f⋆ + ϵ`, the number of calls and the cap `T` are
both at most `C·p·κ·log(2 + ν₀/ϵ)`.

**Formalization Note.** Algorithm 2 is `refineState` (a relation over solver outputs, each free), and a
call happens at `t < T` exactly when `ϵ < ν_t`. -/
theorem lemma_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d m : ℕ) (G : GenRegression n d m), G.IsStanding →
        ∀ (p κ ε ν₀ : ℝ) (x₀ : Fin d → ℝ) (dirs : ℕ → Fin d → ℝ),
          2 ≤ p → 1 ≤ κ → 0 < ε → G.Feasible x₀ → G.obj p x₀ - G.fStar p ≤ ν₀ →
          (∀ t < refineCap p κ ν₀ ε, ε < (refineState G p κ ε x₀ ν₀ dirs t).nu →
            CallSucceeds G p κ (refineState G p κ ε x₀ ν₀ dirs t).x
              (refineState G p κ ε x₀ ν₀ dirs t).nu (dirs t)) →
          G.Feasible (refineState G p κ ε x₀ ν₀ dirs (refineCap p κ ν₀ ε)).x ∧
          G.obj p (refineState G p κ ε x₀ ν₀ dirs (refineCap p κ ν₀ ε)).x ≤ G.fStar p + ε ∧
          (callCount G p κ ε x₀ ν₀ dirs (refineCap p κ ν₀ ε) : ℝ) ≤
            C * p * κ * Real.log (2 + ν₀ / ε) ∧
          (refineCap p κ ν₀ ε : ℝ) ≤ C * p * κ * Real.log (2 + ν₀ / ε) := by sorry

end PNormReg
