-- Prove2me | Theorems.Thm_SunGroupIso_Class2_theorem_2_3
-- name    : SunGroupIso.Class2.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:07:12.242988+00:00
-- url     : https://prove2.me/theorems/3304ac28-766b-48ab-9d61-579c9c667e36
-- title:
--   Theorem 2.3 — [GQSS25, Lemma 5.16]: reduction of alternating tensor isomorphism to restricted instances
-- statement:
--   There are one Turing machine $M$ and one constant $C$ such that for every prime $p$, every $\tau\ge1$ and all non-degenerate alternating $n\times n\times m$ tensors $T,T'$ over $R=\mathbb Z/p^\tau$ with the same complex parameter $c=c_T$: $M$, on the code of $(p,\tau,n,m,T,T')$, outputs within $\lceil p^{Cc^{17/9}(\log p)^{8/9}}\rceil$ steps a list of at most $\lceil p^{Cc^{17/9}(\log p)^{8/9}}\rceil$ tuples $(d,U,U',W,W',P,P')$, $U,U'\in GL(n,R)$, $W,W'\in GL(m,R)$, $P,P'\in M(d\times n,R)$, such that (1) for each, $d\le c^2$ and $((U,U,W)\circ T,(U',U',W')\circ T',P,P')$ is an input instance of the restricted alternating tensor isomorphism problem with $w=\lfloor C\tau^2c^{4/9}(\log p)^2\rfloor$; (2) for every $X\in GL(n,R)$, $Y\in GL(m,R)$ with $(X,X,Y)\circ T=T'$ some listed tuple has $(U'XU^{-1},W'YW^{-1})$ as a solution of its instance.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
--   - reading: w = O(τ²·c_T^{4/9}·(log p)²) → every instance satisfies condition 1 with w = ⌊C·τ²·c^{4/9}·(log p)²⌋; reason: condition 1 only weakens as w grows, so 'some w = O(·)' and 'w equal to the O-bound' are the same requirement
--   - reading: the standing non-degeneracy convention for matrix tuples (§2.1, PDF 10) → NondegenerateTensor T, NondegenerateTensor T' on the slice tuples N_{T,i}; reason: restores the source domain; arbitrary zero padding does not preserve a runtime measured only by c_T
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 2.3, p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Tensor

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Theorem 2.3** (c.f. Lemma 5.16 of [GQSS25]; Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 2.3, pp. 10–11, PDF pp. 12–13).
For alternating tensors `T, T'`, under the standing non-degeneracy convention,  over `R = Z/p^τZ` with the same complex parameter `c_T`, an algorithm with
running time `p^{O(c_T^{17/9}(log p)^{8/9})}` reduces tensor isomorphism to `p^{O(c_T^{17/9}(log p)^{8/9})}`
instances of the restricted alternating tensor isomorphism problem with `d ≤ c_T^2` and
`w = O(τ^2 c_T^{4/9}(log p)^2)`: (1) each instance is `((U,U,W)∘T, (U',U',W')∘T', P, P')`, an input
instance; (2) for every `X, Y` with `(X,X,Y)∘T = T'` some produced instance is solved by
`(U'XU^{-1}, W'YW^{-1})`. One machine and one constant `C` serve every `p, τ, n, m`. -/
theorem theorem_2_3 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p τ n m : ℕ), p.Prime → 0 < τ →
      ∀ T T' : Fin n → Fin n → Fin m → ZMod (p ^ τ),
        IsAltTensor T → IsAltTensor T' → NondegenerateTensor T → NondegenerateTensor T' → cT p T = cT p T' →
        let c : ℝ := cT p T
        let K : ℕ := ppow p (C * c ^ ((17 : ℝ) / 9) * Real.log p ^ ((8 : ℝ) / 9))
        let w : ℕ := ⌊(C : ℝ) * τ ^ 2 * c ^ ((4 : ℝ) / 9) * Real.log p ^ 2⌋₊
        let inp : List Bool := encHeader p τ n m ++ encTensor T ++ encTensor T'
        ∃ L : List (Σ d : ℕ, GL (Fin n) (ZMod (p ^ τ)) × GL (Fin n) (ZMod (p ^ τ)) ×
            GL (Fin m) (ZMod (p ^ τ)) × GL (Fin m) (ZMod (p ^ τ)) ×
            Matrix (Fin d) (Fin n) (ZMod (p ^ τ)) × Matrix (Fin d) (Fin n) (ZMod (p ^ τ))),
          L.length ≤ K ∧
          (∀ (d : ℕ) (U U' : GL (Fin n) (ZMod (p ^ τ))) (W W' : GL (Fin m) (ZMod (p ^ τ))) (P P' : Matrix (Fin d) (Fin n) (ZMod (p ^ τ))), ⟨d, U, U', W, W', P, P'⟩ ∈ L →
            d ≤ cT p T ^ 2 ∧
            IsRestrictedInstance w (actT (U : Matrix _ _ _) U W T) (actT (U' : Matrix _ _ _) U' W' T') P) ∧
          (∀ (X : GL (Fin n) (ZMod (p ^ τ))) (Y : GL (Fin m) (ZMod (p ^ τ))),
            actT (X : Matrix _ _ _) X Y T = T' →
            ∃ (d : ℕ) (U U' : GL (Fin n) (ZMod (p ^ τ))) (W W' : GL (Fin m) (ZMod (p ^ τ))) (P P' : Matrix (Fin d) (Fin n) (ZMod (p ^ τ))), ⟨d, U, U', W, W', P, P'⟩ ∈ L ∧
              IsRestrictedSolution (actT (U : Matrix _ _ _) U W T) (actT (U' : Matrix _ _ _) U' W' T')
                P P' (U' * X * U⁻¹) (W' * Y * W⁻¹)) ∧
          HMBinPacking.OutputsWithin M inp
            (encList (fun x => encodeNat x.1 ++ encMat x.2.1.val ++ encMat x.2.2.1.val ++
              encMat x.2.2.2.1.val ++ encMat x.2.2.2.2.1.val ++ encMat x.2.2.2.2.2.1 ++
              encMat x.2.2.2.2.2.2) L)
            (K) := by sorry

end SunGroupIso.Class2
