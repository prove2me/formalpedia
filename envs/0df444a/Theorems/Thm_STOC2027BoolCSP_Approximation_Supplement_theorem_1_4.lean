-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_theorem_1_4
-- name    : STOC2027BoolCSP.Approximation.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:21.373929+00:00
-- url     : https://prove2.me/theorems/d59fbb38-d36a-4538-a509-635b27198040
-- title:
--   Theorem 1.4 — under UGC, NP-hard Max-$k$-AND gap $\gamma-\varepsilon$ vs. $\beta+\varepsilon$ for even $k\ge4$, hardness ratio $R_k<(k+2)/2^k$
-- statement:
--   Fix an even integer $k\ge4$ and the positive rational constants (2):
--   $$n=k-2,\ t=\frac1{16n^2},\ c=\frac{n(n-1)}4,\ C=2^{k-1}-1,\ d=(k-1)t,\ a=\frac{cd}{C^2},\ x=ad,\ \xi=\frac{x}{8(1+x)}.$$
--   Let $\gamma,\beta$ be the explicit rational constants of (62) and $R_k=\frac{k+2}{2^k}\cdot\frac{1+x/2}{1+7x/8}$. Then:
--
--   1. $t,c,C,d,a,x,\xi>0$;
--   2. $\gamma\ge\dfrac{1+7x/8}{k+2}$ and $\beta\le2^{-k}(1+x/2)$;
--   3. $\beta/\gamma\le R_k$, and $R_k=\dfrac{k+2}{2^k}\Big(1-\dfrac{3x}{8+7x}\Big)<\dfrac{k+2}{2^k}$;
--   4. assuming the Unique Games Conjecture, there is $\varepsilon_0>0$ such that for every $0<\varepsilon<\varepsilon_0$ it is NP-hard to distinguish unweighted Max-$k$-AND instances (every clause a signed conjunction on exactly $k$ distinct variables, weight one) of value at least $\gamma-\varepsilon$ from those of value at most $\beta+\varepsilon$, the value being the largest fraction of simultaneously satisfiable clauses;
--   5. in particular, assuming the Unique Games Conjecture and $\mathrm P\ne\mathrm{NP}$, for every $r>R_k$ no deterministic polynomial-time algorithm returns, on every Boolean Max-$k$-CSP instance with nonnegative rational weights, an assignment of value at least $r\cdot\mathrm{OPT}$.
--
--   This strictly lowers De and Mossel's even-arity bound $(k+2)/2^k$ for every even $k\ge4$.
--
--   Differences from the source:
--   - generalization: there are explicit rational γ, β satisfying the bounds → γ and β are the explicit constants of (62); reason: naming the constants implies their existence
--   - encoding: NP-hard to distinguish value ≥ γ − ε from value ≤ β + ε, instances unweighted with exactly k distinct variables per clause → GapNPHard (Karp reductions from every NP language in Cook's model) for ConjInstance.code with YES/NO restricted to unweighted instances with M ≥ 1, value = OPT/M; reason: Section 10's fraction-of-total-weight convention; the restriction is the strong form the theorem asserts
--   - encoding: for every sufficiently small ε > 0 → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); reason: standard reading
--   - encoding: assuming the Unique Games Conjecture → hypothesis OptInapprox.MaxCut.UGC (Khot's conjecture for bipartite Unique Label Cover); reason: the standard conjecture; the regular loop-free form of Section 14 is derived in the proof
--   - reading: in particular the hardness bound for general Boolean Max-k-CSP is at most R_k → β/γ ≤ R_k, the identity for R_k and R_k < (k+2)/2^k, and: under UGC and P ≠ NP no polynomial-time deterministic algorithm (Cook's model, base instance code) achieves r·OPT for any r > R_k; reason: printed p. 3 defines a hardness bound R_k as excluding every deterministic polynomial-time factor greater than R_k under UGC and P ≠ NP
--   - encoding: define the positive rational constants (2) → the constants as ℚ-valued functions of k, with their positivity as a conclusion; reason: the positivity is asserted by the source
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 2–3 (PDF 5–6), Theorem 1.4 with equations (2), (3) and the following paragraph; proof printed p. 22–33 (PDF 25–36), Sections 11–14, equations (62), (63)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_ConjOpt
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Constants
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_MaxKAND

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- Theorem 1.4 (strict even arity hardness improvement), printed p. 2, proof §§11–14. Fix an even
`k ≥ 4` with the constants (2). The constants are positive; the explicit rational constants
`γ, β` of (62) satisfy `γ ≥ (1 + 7x/8)/(k+2)`, `β ≤ 2^{−k}(1 + x/2)` and `β/γ ≤ R_k`, where
`R_k = ((k+2)/2^k)(1 + x/2)/(1 + 7x/8) = ((k+2)/2^k)(1 − 3x/(8 + 7x)) < (k+2)/2^k`. Assuming the
Unique Games Conjecture, for every sufficiently small `ε > 0` it is NP-hard to distinguish
unweighted Max-`k`-AND instances (clauses on exactly `k` distinct variables) of value at least
`γ − ε` from those of value at most `β + ε`. In particular, under UGC and `P ≠ NP`, no
deterministic polynomial-time algorithm achieves an approximation factor `r > R_k` for Boolean
Max-`k`-CSP. -/
theorem theorem_1_4 (k : ℕ) (hk : 4 ≤ k) (heven : Even k) :
    (0 < tC k ∧ 0 < cC k ∧ 0 < bigC k ∧ 0 < dC k ∧ 0 < aC k ∧ 0 < xC k ∧ 0 < xiC k) ∧
    (1 + 7 * xC k / 8) / ((k : ℚ) + 2) ≤ gammaC k ∧
    betaC k ≤ (1 / 2 ^ k) * (1 + xC k / 2) ∧
    betaC k / gammaC k ≤ ratioR k ∧
    ratioR k = (((k : ℚ) + 2) / 2 ^ k) * (1 - 3 * xC k / (8 + 7 * xC k)) ∧
    ratioR k < ((k : ℚ) + 2) / 2 ^ k ∧
    (OptInapprox.MaxCut.UGC →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        OptInapprox.MaxCut.GapNPHard (fun C : ConjInstance k => C.code)
          (AndYes k ((gammaC k : ℝ) - ε)) (AndNo k ((betaC k : ℝ) + ε))) ∧
    (OptInapprox.MaxCut.UGC → PneNP → ∀ r : ℝ, (ratioR k : ℝ) < r →
      ¬ ∃ A : List Bool → List Bool, CookPvsNP.PolyTimeComputable A ∧
        ∀ I : Instance, I.IsMaxkCSP k →
          r * I.opt ≤ I.val (decodeAssignment I.n (A (instanceCode I)))) := by sorry

end STOC2027BoolCSP.Approximation.Supplement
