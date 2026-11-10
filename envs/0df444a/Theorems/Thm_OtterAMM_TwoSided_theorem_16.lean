-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_theorem_16
-- name    : OtterAMM.TwoSided.theorem_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:07.8608+00:00
-- url     : https://prove2.me/theorems/b6a8f851-8f0f-4fea-9799-c99aef391ddd
-- title:
--   Theorem 16 — the one-sided VCG auction: well-formed (16), IR, feasible (17), submodular welfare, UIC with sybils
-- statement:
--   Let $G$ be a one-sided compensation curve ($G:[0,\infty)\to\mathbb R_{\ge0}$ continuous, strictly increasing, concave, $G(0)=0$, $\sigma_0=G'_+(0)\in(0,\infty)$), only sell-Y bids, and an admissible selection rule. Then:
--
--   (a) for every finite bid set $S$ and $i\in S$:
--   $$0\le y^*_i\le\tilde q_i,\qquad 0\le x^*_i\le G(Y^*)-G(Y^*-y^*_i)\le\sigma_0y^*_i;\qquad(16)$$
--   (b) under truthful reporting every user's utility (2) is nonnegative;
--   (c) $\sum_ix^*_i\le G(Y^*)$ (17);
--   (d) for any fixed asks and budgets, the set function $S\mapsto W_G(S)$ is normalized ($W_G(\emptyset)=0$), monotone, and submodular ($W_G(S\cup T)+W_G(S\cap T)\le W_G(S)+W_G(T)$);
--   (e) UIC: for every finite set $O$ of other sell-Y reports, every true type $(v,q)\in\mathbb R^2_{\ge0}$ and every finite, possibly empty, set $D$ of fresh sell-Y identities with arbitrary reports in $\mathbb R^2_{\ge0}$, the user's utility (2) from $D$ (which is $-\infty$ when the aggregate sale exceeds $q$) is at most its utility from a single truthful identity.
--
--   It is applied in §6 to $\tilde F^M_Y$ and (roles of $X,Y$ swapped) $\tilde H^M_X$.
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: G : [0, +∞) → ℝ≥0 → G : ℝ → ℝ with every condition imposed on [0, +∞) (codomain ℝ≥0 implied by monotonicity and G(0) = 0); σ0 = derivWithin G (Ici 0) 0; reason: values off [0, +∞) are never used
--   - encoding: W_F(S) = max over the box 0 ≤ y_i ≤ q̃_i (Eq. (3)) → W = sSup of the welfare over the box; reason: for a one-sided curve the welfare is continuous on a compact nonempty box, so the supremum is the attained maximum
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
--   - encoding: (d): W_F a set function on finite sets of bids with given asks and budgets → asks and budgets are functions on all labels, nonnegative everywhere; W G S a q only reads them on S; reason: every finite bid family extends to such functions, so the set function is the same
--   - encoding: (b): truthful utility → util (rep i) of the singleton {i} in the truthful profile, i.e. Eq. (2) with the report as type; reason: Eq. (2) is the paper's utility; no instance changes
--   - encoding: reports in ℝ²≥0 (§2, §3.1); only sell-Y bids are allowed → hypotheses (rep i).dir = Dir.sellY ∧ (rep i).Valid on the block, and the same on O and on the deviation D in (e); 0 ≤ v, 0 ≤ q for the true type; reason: the paper's domain of reports and the theorem's 'Suppose that only sell-Y bids are allowed', not an extra condition
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 18, Theorem 16 (PDF 20)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Theorem 16 (p. 18): the one-sided VCG auction on a one-sided curve `G` (sell-Y bids only)
is (a) well-formed, Eq. (16); (b) individually rational; (c) feasible, Eq. (17); (d) its welfare
`W_G` is normalized, monotone and submodular; (e) UIC against misreports and sybil identities
(Eq. (2) utility, `−∞` when the aggregate sale exceeds the true budget). -/
theorem theorem_16 (G : ℝ → ℝ) (hG : IsOneSidedCurve G) (sel : SelRule) (hsel : sel.Admissible) :
    -- (a), (b), (c) on every finite set `S` of sell-Y bids
    (∀ (S : Finset Ident) (rep : Ident → Report),
      (∀ i ∈ S, (rep i).dir = Dir.sellY ∧ (rep i).Valid) →
      (∀ i ∈ S,
          0 ≤ vcgAlloc sel G S (askOf rep) (budgetOf rep) i ∧
          vcgAlloc sel G S (askOf rep) (budgetOf rep) i ≤ (rep i).budget ∧
          0 ≤ vcgComp sel G S (askOf rep) (budgetOf rep) i ∧
          vcgComp sel G S (askOf rep) (budgetOf rep) i ≤
            G (vcgTotal sel G S (askOf rep) (budgetOf rep)) -
              G (vcgTotal sel G S (askOf rep) (budgetOf rep) -
                vcgAlloc sel G S (askOf rep) (budgetOf rep) i) ∧
          G (vcgTotal sel G S (askOf rep) (budgetOf rep)) -
              G (vcgTotal sel G S (askOf rep) (budgetOf rep) -
                vcgAlloc sel G S (askOf rep) (budgetOf rep) i) ≤
            slope0 G * vcgAlloc sel G S (askOf rep) (budgetOf rep) i) ∧
      (∀ i ∈ S, (0 : EReal) ≤ util (rep i) rep (oneSidedOutcome sel G S rep) {i}) ∧
      ∑ i ∈ S, vcgComp sel G S (askOf rep) (budgetOf rep) i ≤
        G (vcgTotal sel G S (askOf rep) (budgetOf rep))) ∧
    -- (d) `W_G` is normalized, monotone and submodular
    (∀ a q : Ident → ℝ, (∀ i, 0 ≤ a i ∧ 0 ≤ q i) →
      W G ∅ a q = 0 ∧
      (∀ S T : Finset Ident, S ⊆ T → W G S a q ≤ W G T a q) ∧
      (∀ S T : Finset Ident, W G (S ∪ T) a q + W G (S ∩ T) a q ≤ W G S a q + W G T a q)) ∧
    -- (e) UIC with sybil identities (sell-Y bids only)
    (∀ (O : Finset Ident) (rep : Ident → Report) (v q : ℝ) (i0 : Ident) (D : Finset Ident)
        (dev : Ident → Report),
      (∀ j ∈ O, (rep j).dir = Dir.sellY ∧ (rep j).Valid) → 0 ≤ v → 0 ≤ q → i0 ∉ O →
      Disjoint D O → (∀ j ∈ D, (dev j).dir = Dir.sellY ∧ (dev j).Valid) →
      util ⟨Dir.sellY, v, q⟩ (overlay D dev rep)
          (oneSidedOutcome sel G (D ∪ O) (overlay D dev rep)) D ≤
        util ⟨Dir.sellY, v, q⟩ (Function.update rep i0 ⟨Dir.sellY, v, q⟩)
          (oneSidedOutcome sel G (insert i0 O) (Function.update rep i0 ⟨Dir.sellY, v, q⟩)) {i0}) := by sorry

end OtterAMM.TwoSided
