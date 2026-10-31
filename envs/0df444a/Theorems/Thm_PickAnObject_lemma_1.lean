-- Prove2me | Theorems.Thm_PickAnObject_lemma_1
-- name    : PickAnObject.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:38.821971+00:00
-- url     : https://prove2.me/theorems/26b7e4c2-6357-44c2-bff2-ec0905e63029
-- title:
--   Lemma 1: outcomes after any history are $\varphi_{a^*}(\gamma\oplus P_{a^*}|_{O\setminus I},P'_{-a^*})$ and $\varphi_{a^*}(\gamma\oplus P^*|_{O\setminus I},P'_{-a^*})$
-- statement:
--   Let the menu function $S$ sequentialize the rule $\varphi$, and let $h^A$ be any collective history of $S$. Let $P$ be any preference profile, $\sigma^P$ the straightforward strategy profile with respect to $P$, $a^*$ any agent and $\sigma'$ any strategy for $a^*$. Then there are a tuple $\gamma$ of distinct object types (with set of entries $I$), a preference $P^*$ and a profile $P'$ of the other agents such that
--
--   $$\mathcal O_{a^*}|_{h^A}\bigl(\sigma^P_{a^*},\sigma^P_{-a^*}\bigr)=\varphi_{a^*}\bigl(\gamma\oplus P_{a^*}|_{O\setminus I},\,P'_{-a^*}\bigr)$$
--   and
--   $$\mathcal O_{a^*}|_{h^A}\bigl(\sigma',\sigma^P_{-a^*}\bigr)=\varphi_{a^*}\bigl(\gamma\oplus P^*|_{O\setminus I},\,P'_{-a^*}\bigr).$$
--
--   The same $\gamma$ and the same $P'_{-a^*}$ appear in both equations. Combined with Corollary 1 this reduces equilibrium play after an arbitrary history to a strategy-proofness comparison.
--
--   Differences from the source:
--   - reading: "a set of object types $I\subseteq O$, a tuple $\gamma$ with elements of $O$" → $\gamma$ duplicate-free with $I$ its set of entries; reason: the proof ends "For $I=\{o\in\gamma^h_{a^*}\}$" and the use on p.45 says "a tuple $\gamma$ with the elements in $I$"; otherwise $\gamma\oplus P|_{O\setminus I}$ is not a preference
--   - reading: "$\gamma\oplus P|_{O\setminus I}$" → $\gamma\oplus P_{a^*}|_{O\setminus I}$; reason: $P$ there is agent $a^*$'s preference
--   - generalization: $h^A\in H^A_{\mathbb S}$ → every reachable history, $h^{A-\varnothing}$ included; reason: at $h^{A-\varnothing}$ the claim is the case of the empty tuple; it specializes to the source's histories
--   - encoding: a profile $P'_{-a^*}$ for agents other than $a^*$ → a full profile $P'$ whose entry at $a^*$ is overwritten; reason: only $P'_{-a^*}$ is used
--   - encoding: strategies → functions of the agent's own history and menu that pick from every non-empty menu; outcome → the $|A|\cdot|O|+1$-period run; reachable histories → an inductive predicate; menu functions → `IsMenuFunction` (shrinking constraint at every non-empty list history, none where an agent has faced no menu); reason: the paper's strategy domain (p.18) and run (pp.10–11); the run has stopped after that many periods, and menus at histories the mechanism never reaches affect neither the run nor the outcome
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, App. A, Lemma 1, p.44 (proof pp.44–45, equations (1)–(2))

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Lemma 1**, Bó–Hakimov, arXiv:2012.01025v4, App. A, p.44: "Let `S_φ` be a pick-an-object
mechanism that sequentializes `φ`, and `h^A ∈ H^A_S` be any collective history of `S_φ`. Let `P`
be any preference profile, `σ^P` be the straightforward strategy profile with respect to `P`,
`a*` be any agent, and `σ'` be any other strategy for `a*`. Then there is a set of object types
`I ⊆ O`, a tuple `γ` with elements of `O`, a preference `P* ∈ 𝒫`, and a preference profile for
agents other than `a*` `P'_{−a*}` such that:
`𝒪_{a*}|_{h^A}(σ^P_{a*}, σ^P_{−a*}) = φ_{a*}(γ ⊕ P|_{O∖I}, P'_{−a*})` and
`𝒪_{a*}|_{h^A}(σ', σ^P_{−a*}) = φ_{a*}(γ ⊕ P*|_{O∖I}, P'_{−a*})`."

**Formalization Note.** `γ` lists the elements of `I` without repetition (the proof's
"For `I = {o ∈ γ^h_{a*}}`", p.45, and "a tuple `γ` with the elements in `I`", p.45), so `I` is
not a separate variable; `P|_{O∖I}` is `P_{a*}|_{O∖I}`. The profile `P'` is a full profile
whose entry at `a*` is overwritten, so only `P'_{−a*}` matters. `σ'` ranges over valid strategies,
and `h^A` over all reachable histories including `h^{A−∅}`. -/
theorem lemma_1 {A Obj : Type*} [Fintype A] [DecidableEq A] [Fintype Obj] [DecidableEq Obj]
    (φ : Rule A Obj) (S : MenuFunction A Obj) (hS : Sequentializes S φ)
    (h : CollectiveHistory A Obj) (hh : Reachable S h) (P : Profile A Obj) (astar : A)
    (σ' : Strategy Obj) (hσ' : IsValidStrategy σ') :
    ∃ (γ : List (Option Obj)) (Pstar : Pref Obj) (P' : Profile A Obj),
      γ.Nodup ∧
      outcome S (fun b => straightforward (P b)) h astar =
        φ (Function.update P' astar (prefixPref γ (P astar))) astar ∧
      outcome S (Function.update (fun b => straightforward (P b)) astar σ') h astar =
        φ (Function.update P' astar (prefixPref γ Pstar)) astar := by sorry

end PickAnObject
