-- Prove2me | Theorems.Thm_SubspaceConv_Supplement_theorem_5
-- name    : SubspaceConv.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:50:38.278533+00:00
-- url     : https://prove2.me/theorems/511f6e53-1ef7-4a7e-9d5b-62f426559b60
-- title:
--   Theorem 5 — exact-span counts in $O_q(\ell+N_q(n)\log N_q(n))$ operations over $\mathbb Q$
-- statement:
--   Let $v_1, \dots, v_\ell \in \mathbb F_q^n$; the vectors may repeat and may be zero. For every subspace $U \le \mathbb F_q^n$ let
--
--   $$C(U) = \#\{A \subseteq [\ell] : \operatorname{span}\{v_i : i \in A\} = U\}.$$
--
--   Then all the numbers $C(U)$, $U \in \mathrm{Gr}_q(n)$, can be computed in
--
--   $$O_q\big(\ell + N_q(n) \log N_q(n)\big)$$
--
--   arithmetic operations over $\mathbb Q$, where $N_q(n)$ is the number of subspaces of $\mathbb F_q^n$.
--
--   For a uniformly random subset of the indices, $C(U)/2^\ell$ is the probability that its span is exactly $U$.
--
--   **Formalization Note** "Arithmetic operations over $\mathbb Q$" is an arithmetic straight-line program (`SubspaceConv.Supplement.ArithSLP`) with no inputs, evaluated over $\mathbb Q$ with $p^{-1} = 1/p$, whose gates may be chosen depending on the vectors (normalizing and indexing the vectors is charged separately by the paper, p.15). It contains no integer-scaling gate, so its only free constants are $0$ and $1$; additions, subtractions, multiplications and multiplications by $1/p$ cost one each. $\mathrm{Gr}_q(n)$ is the published `SubLE F n n` and $N_q(n)$ the published `Mq F n n`. One constant depends only on the field; $\log$ is natural.
--
--   Differences from the source:
--   - reading: arithmetic operations over Q (the vectors given) → a straight-line program over ℚ with no inputs, wiring chosen from (n, ℓ, v), free constants 0 and 1 only, no integer-scaling gate; reason: the paper charges indexing separately (p.15); with free integer scalings each output would cost one gate, so this is the non-trivial reading, and the proof of p.15 (doublings, two transforms) fits it
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), Theorem 5, p.14–15 (PDF p.15–16)

import Mathlib
import Definitions.Def_SubspaceConv_SubLE
import Definitions.Def_SubspaceConv_Mq
import Definitions.Def_SubspaceConv_Supplement_ArithSLP
import Definitions.Def_SubspaceConv_Supplement_spanCount

set_option autoImplicit false

namespace SubspaceConv.Supplement

/-- **Theorem 5** (Counting exact spans), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.14–15 (PDF p.15–16). Given
`v_1, …, v_ℓ ∈ F_q^n`, all numbers `C(U) = #{A ⊆ [ℓ] : span{v_i : i ∈ A} = U}`, `U ∈ Gr_q(n)`, can be
computed in `O_q(ℓ + N_q(n) log N_q(n))` arithmetic operations over `Q`. The vectors may repeat
and may be zero.

**Formalization Note** "Arithmetic operations over `Q`" is an arithmetic straight-line program
`SubspaceConv.Supplement.ArithSLP` with no inputs, evaluated over `ℚ` with `pinv = 1/p`
(`p = ringChar F`); its wiring may depend on `(n, ℓ, v)` (the paper charges normalizing and
indexing the vectors separately, "in addition", p.15). It has no integer-scaling gate
(`NoZmul`), so its only free constants are `0` and `1`; every `add`, `sub`, `mul`, `invp` costs
one. `Gr_q(n)` is the set of all subspaces, the published `SubLE F n n`, and `N_q(n)` is the
published `Mq F n n`. One real constant `C` depends only on `F`; `log` is natural. -/
theorem theorem_5 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ (n ℓ : ℕ) (v : Fin ℓ → Fin n → F),
      ∃ P : ArithSLP Empty (SubLE F n n),
        P.WellFormed ∧ P.NoZmul ∧
        (P.cost : ℝ) ≤ C * ((ℓ : ℝ) + (Mq F n n : ℝ) * Real.log (Mq F n n : ℝ)) ∧
        ∀ U : SubLE F n n,
          P.eval ((ringChar F : ℚ)⁻¹) (fun e => Empty.elim e) U = (spanCount v U.1 : ℚ) := by sorry

end SubspaceConv.Supplement
