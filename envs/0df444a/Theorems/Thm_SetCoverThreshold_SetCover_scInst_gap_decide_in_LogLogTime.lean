-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_scInst_gap_decide_in_LogLogTime
-- name    : SetCoverThreshold.SetCover.scInst_gap_decide_in_LogLogTime
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T19:44:40.717243+00:00
-- url     : https://prove2.me/theorems/25b72ba8-36f5-49f5-aba3-d5ef2211bb6e
-- title:
--   Quasi-polynomial-time decision from the §4 Set Cover approximation gap (Feige 1998, Theorem 4.4)
-- statement:
--   Quasi-polynomial-time (TIME(n^{O(log log n)})) decision from the §4 Set Cover approximation gap (Feige 1998, Theorem 4.4, p. 647): given the Naor–Schulman–Srinivasan partition-system generator $F$ for $k \ge 2$ provers with parameter $\eta = \min(\varepsilon / 4, 1 / 4) > 0$, the parallel repetition constant $c > 0$ of Lemma 4.1, a polynomial-time $(1 - \varepsilon) \ln n$-approximation estimator $A$ for Set Cover, and a polynomial-time reduction $f : \Sigma^* \to \text{Formula5}$ whose §4 instances $\mathrm{scInst}(f(x), \mathrm{code}, P_0)$ satisfy the gap condition, the language $L$ lies in $\text{LogLogTime}(\Sigma)$.
-- source:
--   Feige 1998, A Threshold of ln n for Approximating Set Cover, J. ACM 45(4): 634–652, Theorem 4.4, p. 647

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_SetCoverThreshold_SetCover_Reduction
import Definitions.Def_SetCoverThreshold_SetCover_Theorem44

namespace SetCoverThreshold.SetCover

open CookPvsNP

/-- **Quasi-polynomial-time (`TIME(n^{O(log log n)})`) decision from the §4 Set Cover approximation
gap** (Feige 1998, Theorem 4.4, p. 647): given the Naor–Schulman–Srinivasan partition-system
generator `F` for `k ≥ 2` provers with parameter `η = min (ε / 4) (1 / 4) > 0`, the parallel
repetition constant `c > 0` of Lemma 4.1, a polynomial-time `(1 - ε) ln n`-approximation estimator
`A` for Set Cover, and a polynomial-time reduction `f : List Sym → Formula5` whose §4 instances
`scInst (f x) code (fun _ => P₀)` have a cover of size at most `k Q` (hence estimator output at
most `(1 - ε) ln N · |C|`) on `x ∈ L` and estimator output at least `(1 - 2η) k Q ln m'` on
`x ∉ L`, the language `L` lies in `LogLogTime Sym`. -/
theorem scInst_gap_decide_in_LogLogTime
    (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : Lang Sym)
    (ε ε' c : ℝ) (hε : 0 < ε) (hε' : 0 < ε') (hc : 0 < c)
    (k m₀ n₀ : ℕ) (hk : 2 ≤ k)
    (F : List Bool → List (Option (Fin k))) (hF : PolyTimeComputable F)
    (hNaorSpec : ∀ m L_part : ℕ, m₀ ≤ m → L_part ≤ Nat.log 2 m →
      ∃ (m' d : ℕ) (P₀ : PartitionSystem m' L_part k d),
        m ≤ m' ∧ F (unaryPair m L_part) = encodeTable P₀.table ∧
          (1 - min (ε / 4) (1 / 4)) * k * Real.log m' ≤ d)
    (A : List (Option Bool) → List Unit) (hA : PolyTimeComputable A)
    (f : List Sym → Formula5) (hf : PolyTimeComputable (fun x => encodeCNF (f x).toCNF))
    (hGap : ∀ (x : List Sym) (ℓ m' d : ℕ) (code : Fin k → Fin ℓ → Bool),
      IsCode ℓ k code →
      ∀ P₀ : PartitionSystem m' (2 ^ ℓ) k d,
        let I := scInst (f x) code (fun _ => P₀)
        n₀ ≤ I.n →
          (x ∈ L → ∃ C : Finset (Fin I.sets.length),
            I.IsCover C ∧ C.card ≤ k * (f x).numQuestions ℓ ∧
              ((A I.encode).length : ℝ) ≤ (1 - ε) * Real.log I.n * (C.card : ℝ)) ∧
          ((1 - min (ε / 4) (1 / 4)) * k * Real.log m' ≤ d →
            (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) <
              2 * (2 * min (ε / 4) (1 / 4)) / (k * Real.log m') ^ 2 →
            x ∉ L →
              (1 - 2 * min (ε / 4) (1 / 4)) * k * (f x).numQuestions ℓ * Real.log m' ≤
                ((A I.encode).length : ℝ))) :
    L ∈ LogLogTime Sym := by sorry

end SetCoverThreshold.SetCover
