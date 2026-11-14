-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deletion_sensitive_indices_have_short_certificate
-- name    : StabilityDichotomies.Bijunctive.graph_deletion_sensitive_indices_have_short_certificate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:07:49.208907+00:00
-- url     : https://prove2.me/theorems/12d90ceb-bd35-4cee-b96f-baa525327064
-- title:
--   Sensitive graph deletions lie on a short winning-path certificate
-- statement:
--   Suppose graph arcs carry deletion labels and deleting one label retains all arcs carrying a different label. For a variable with positive winning score, all label deletions that change its output lie in a finite set of at most $n$ labels, where $n$ is strictly smaller than the shift of a feasible maximizing root. This establishes the deterministic graph-deletion certificate used in the sensitivity proof.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.graph_deletion_sensitive_indices_have_short_certificate
    {Γ : Language} {V ι : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (Gdel : ι → Instance Γ V)
    (δ : Literal V → ℝ) (label : ι → Literal V → Literal V → Prop)
    (hsub : ∀ j a b, implicationArc rep (Gdel j) a b → implicationArc rep G a b)
    (hlabel : ∀ a b, implicationArc rep G a b → ∃ j, label j a b)
    (hretain : ∀ i j a b, i ≠ j → label i a b → implicationArc rep (Gdel j) a b)
    (v : V) (w : Bool)
    (hw : w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)))
    (hpos : (0 : WithBot ℝ) < literalScore rep G F δ (v,w)) :
    ∃ root : Literal V, ∃ n : ℕ, ∃ S : Finset ι,
      S.card ≤ n ∧ (n : ℝ) < δ root ∧
      ∀ j ∉ S, decide (literalScore rep (Gdel j) F δ (v,false) <
        literalScore rep (Gdel j) F δ (v,true)) = w := by
  sorry
