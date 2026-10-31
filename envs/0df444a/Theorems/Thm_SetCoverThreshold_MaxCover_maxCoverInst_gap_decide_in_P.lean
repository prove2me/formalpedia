-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_maxCoverInst_gap_decide_in_P
-- name    : SetCoverThreshold.MaxCover.maxCoverInst_gap_decide_in_P
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:44.858162+00:00
-- url     : https://prove2.me/theorems/0a0a9aab-eaf5-4309-b736-a2d0ac51bb48
-- title:
--   Polynomial-Time Decision from Max k-Cover Gap (Theorem 5.3)
-- statement:
--   This theorem establishes that an approximation algorithm separating the completeness and soundness thresholds of the Max $k$-Cover reduction instance yields a polynomial-time decision procedure for the underlying language $L$ (Feige 1998, Section 5, p. 649, proof of Theorem 5.3).
--
--   Specifically, for fixed parameters $k \ge 1$, $\ell \ge 1$, code $C$, and gap $\varepsilon > 0$:
--   Let $f : \{0,1\}^* \to \text{Formula5}$ be a polynomial-time reduction producing non-empty 3CNF-5 formulas, and let $A$ be a polynomial-time unary estimator such that on the encoded instance $\mathcal{I}_x = \text{maxCoverInst}(f(x), C)$ of size $N_x$:
--   - If $x \in L$, then $|A(\text{encode}(\mathcal{I}_x))| \ge (1 - 1/e + \varepsilon) N_x$;
--   - If $x \notin L$, then $|A(\text{encode}(\mathcal{I}_x))| \le (1 - 1/e + \varepsilon/2) N_x$.
--
--   Then the language $L$ is decidable in deterministic polynomial time:
--   $$
--   L \in \mathbf{P}.
--   $$
-- source:
--   Uriel Feige, A Threshold of ln n for Approximating Set Cover, Journal of the ACM 45(4):634-652 (1998), p. 649, proof of Theorem 5.3

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction
import Definitions.Def_SetCoverThreshold_MaxCover_Theorem53

open CookPvsNP

namespace SetCoverThreshold.MaxCover

theorem maxCoverInst_gap_decide_in_P (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ)
    (code : Fin k → Fin ℓ → Bool) (hcode : IsCode code) (ε : ℝ) (hε : 0 < ε)
    (A : List Sym → List Unit) (hA : PolyTimeComputable A)
    (L : Lang Bool) (f : List Bool → Formula5)
    (hf_poly : PolyTimeComputable (fun x => encodeCNF (f x).toCNF))
    (hM : ∀ x : List Bool, 1 ≤ (f x).M)
    (hGap : ∀ x : List Bool,
      (x ∈ L → (1 - Real.exp (-1) + ε) * ((maxCoverInst (f x) code).n : ℝ) ≤
        ((A (encode (maxCoverInst (f x) code))).length : ℝ)) ∧
      (x ∉ L → ((A (encode (maxCoverInst (f x) code))).length : ℝ) ≤
        (1 - Real.exp (-1) + ε / 2) * ((maxCoverInst (f x) code).n : ℝ))) :
    L ∈ P Bool := by sorry

end SetCoverThreshold.MaxCover
