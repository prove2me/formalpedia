-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_theorem_I_1
-- name    : ProcureAssort.Hotelling.Supplement.theorem_I_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:45:21.116148+00:00
-- url     : https://prove2.me/theorems/f571af82-5238-4b1a-917a-be96d021447c
-- title:
--   Theorem I.1 — Vertical-demand linear-pricing implementation
-- statement:
--   Let $n\ge2$ suppliers have arbitrary strictly increasing qualities $\alpha_1<\cdots<\alpha_n$ and independent regular finite cost distributions. Consumers are uniform on $[0,1]$ and buy one unit with utility $u\alpha_i-p_i$. Set $b^*=\min_{i<n}(\alpha_{i+1}-\alpha_i)$, and at a profile $\theta$ write $s_i=(v_{i+1}(\theta_{i+1})-v_i(\theta_i))/(\alpha_{i+1}-\alpha_i)$.
--
--   Suppose there exist $\theta$ and $c^*\in\mathbb R$ such that
--
--   $$s_{i+1}>c^*+s_i\ (1\le i\le n-2),\qquad s_1>c^*,\qquad s_{n-1}<1-c^*.$$
--
--   Every supplier must have at least three types, with every adjacent virtual-cost increment at most $c^*b^*/8$. Then $OPT(DecLin)=OPT(Cent)$. The qualities have no sign restriction. This is the vertical-demand companion theorem.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: OPT denotes an actual optimal value → equality of the published real suprema together with nonempty bounded-above feasible objective sets; reason: compact finite-dimensional consumption and interim IR bound the objectives; the extra clauses rule out junk real suprema without assuming boundedness
--   - reading: every θ_i^j in condition 2, followed by θ_i^{j+1} → consecutive supported pairs with both entries present; reason: the terminal successor is undefined; p. 61 uses the same adjacent-gap condition as Theorem 4.1, whose range is explicitly j less than the support size
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem I.1, p. 61

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Vertical

namespace ProcureAssort.Hotelling.Supplement

theorem theorem_I_1 (n : ℕ) (hn : 2 ≤ n) (alpha : Fin n → ℝ)
    (hAlpha : StrictMono alpha) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (hConditions : ∃ (θ : Profile Θ) (c : ℝ),
      (∀ (k : ℕ) (hk : k+2 < n),
        c + qualitySlope alpha (vvec Θ f θ) k (by omega) <
          qualitySlope alpha (vvec Θ f θ) (k+1) hk) ∧
      c < qualitySlope alpha (vvec Θ f θ) 0 (by omega) ∧
      qualitySlope alpha (vvec Θ f θ) (n-2) (by omega) < 1-c ∧
      (∀ i, 3 ≤ (Θ i).card) ∧
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        virtualCost Θ f i b - virtualCost Θ f i a ≤ c * cstar alpha hn / 8)) :
    optDecLin Θ f (verticalGCS alpha) (simplex n) =
      optCent Θ f (verticalGCS alpha) (simplex n) ∧
    ValuesWellDefined Θ f (verticalGCS alpha) := by sorry

end ProcureAssort.Hotelling.Supplement
