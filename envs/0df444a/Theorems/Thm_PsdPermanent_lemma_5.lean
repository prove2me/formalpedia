-- Prove2me | Theorems.Thm_PsdPermanent_lemma_5
-- name    : PsdPermanent.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:30.008653+00:00
-- url     : https://prove2.me/theorems/0c2c4d8d-e89b-44f7-95dc-e65ee0007e93
-- title:
--   Lemma 5 — the maximum exists and does not depend on the factor
-- statement:
--   Assume $v_i\ne0$ for all $i$ and that $V$ has full column rank. Then the maximum in Eq. (4) is finite and attained. Moreover $\Phi(V)$ depends only on $A=VV^\dagger$: if $W$ is another full-rank factor with $WW^\dagger=VV^\dagger$, then $\Phi(W)=\Phi(V)$.
--
--   This makes $\Phi(A)$ and $\widehat P(A)$ functions of $A$.
--
--   Differences from the source:
--   - encoding: v_i†Xv_i, det X, trX → real parts of (V X V†)_ii, det X, trace X; reason: all three are real on positive definite X
--   - encoding: the maximum is finite and attained → the real supremum Phi V is the greatest element of the set of values; reason: IsGreatest states both
--   - generalization: W another full-rank factor, of the same shape as V → W with its own number of columns d′; reason: equal sizes are a special case, and d′ = d follows
--   - generalization: H_d^{++} defined for d ≥ 1 (§3) → d = 0 allowed, the empty matrix being positive definite with det = 1; reason: the d ≥ 1 statements are a special case; d = 0 is the one-point space (and forces n = 0 where rows are nonzero)
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 5, p.6

import Mathlib
import Definitions.Def_PsdPermanent_phi
import Definitions.Def_PsdPermanent_Phi__d25d42
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Lemma 5 (Existence and invariance).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 5, p.6: "Assume v_i ≠ 0 for all i and that V has full column rank. Then the maximum in Eq. (4) is finite and
attained. Moreover Φ(V) depends only on A = V V†, not on the particular full-rank factor V."

**Formalization Note.** `IsGreatest` is what makes the real `sSup` of `PsdPermanent.Phi` the paper's `max`. The second
factor `W` has its own column count `d'`; `d' = d` is a consequence, not a hypothesis. -/
theorem lemma_5 {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hrank : V.rank = d) (hV : ∀ i, V i ≠ 0) :
    IsGreatest (phi V '' {X : Matrix (Fin d) (Fin d) ℂ | X.PosDef}) (Phi V) ∧
      ∀ (d' : ℕ) (W : Matrix (Fin n) (Fin d') ℂ), W.rank = d' → W * Wᴴ = V * Vᴴ → Phi W = Phi V := by sorry

end PsdPermanent
