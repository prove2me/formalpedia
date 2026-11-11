-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_29
-- name    : SmallBiasPRF.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:40.585471+00:00
-- url     : https://prove2.me/theorems/81f52695-6ded-4e50-8e91-c675503509b7
-- title:
--   Lemma 29 — the potential inequalities with factor $95/96$
-- statement:
--   Let $B\subseteq\mathbb F_2^n$ be nonempty, $S:B\to\mathbb F_3$, and let $\mathcal U$ be a nonempty multiset (with multiplicities) of linear updates $B\to\mathbb F_2$. Assume that, if $\mathrm{gap}_B(S)\ge1$, then $|\{\{U\in\mathcal U:P_U\in N_B(S)\}\}|\le\tfrac9{16}|\mathcal U|$. Then
--
--   $$\mathop{\mathbb E}_{U\in\mathcal U}\mathop{\mathbb E}_{\rho\in\mathbb F_3}\big[\Lambda_B(S+\rho U)^2\,\Psi_B(S+\rho U)\big]\le\frac{95}{96}\Psi_B(S),\tag{29}$$
--
--   $$\Lambda_B(S)^2\mathop{\mathbb E}_{U\in\mathcal U}\mathop{\mathbb E}_{\rho\in\mathbb F_3}\big[\Psi_B(S+\rho U)\big]\le\frac{95}{96}\Psi_B(S).\tag{30}$$
--
--   These are the two pointwise inequalities of the weighted Schur test that proves $\|K_B\|_{op}\le 95/96$ (Lemma 16).
--
--   **Formalization Note** The statement holds for every basis of $V_B^*$ and every field $K$ of characteristic $2$ containing $\omega$ with $\omega^2+\omega+1=0$; states are total functions read on $B$. The multiset is a family indexed by a nonempty finite type (multiplicity = number of indices), and expectations are uniform averages.
--
--   Differences from the source:
--   - generalization: F₄ = F₂(ω) with ω² + ω + 1 = 0 → any field K with CharP K 2 and an element ω with ω² + ω + 1 = 0; reason: every such K contains the subfield F₂(ω) ≅ F₄, all polynomials involved have coefficients there, and degrees and kernels do not change under the field extension; K = F₄ is the paper's case
--   - reading: “choose a basis X_{B,1}, …, X_{B,D_B} of V_B*” → the statement holds for every basis X : Basis ι (ZMod 2) (Dual V_B), ι any finite index type; reason: the paper fixes an arbitrary basis; the universal reading is the strongest and specializes to any chosen basis indexed by [D_B]
--   - encoding: R_B = F₄[X_{B,1}, …, X_{B,D_B}]/(X²_{B,i} − X_{B,i}) as multilinear polynomials; deg of the zero polynomial is 0; S : B → F₃ → coefficient maps Finset ι → K with product X_J·X_L = X_{J∪L}; deg = largest |I| with nonzero coefficient (0 for the zero polynomial); S a total function F₂ⁿ → ZMod 3 read on B; reason: the multilinear representatives of the quotient ring; same polynomials, products and degrees
--   - encoding: a linear update U : B → F₂ (extends to a functional in V_B*) and its linear polynomial P_U → the update is given by its extension L ∈ V_B* (updOfDual L), and P_U ∈ N_B(S) is L ∈ Nspace X ω S; reason: the extension is unique because B spans V_B, so linear updates and functionals correspond bijectively on B
--   - encoding: a nonempty multiset 𝒰 of linear updates with multiplicities → a family L : κ → V_B* over a nonempty finite index type κ; reason: a multiset is a finite indexed family up to reindexing; averages and counts are the same
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 29, displays (29)–(30), p.33 (PDF 36)

import Mathlib
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_Lambda
import Definitions.Def_SmallBiasPRF_statePoly

namespace SmallBiasPRF

/-- **Lemma 29** (potential inequalities), p.33 (PDF p.36).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 29, p.33 (PDF p.36).

Let `S : B → 𝔽₃` and let `𝒰` be a nonempty multiset, with multiplicities, of linear updates, each
mapping `B` to `𝔽₂`. Assume that, if `gap_B(S) ≥ 1`, then
`|{{U ∈ 𝒰 : P_U ∈ N_B(S)}}| ≤ (9/16)|𝒰|`. Then
`E_{U∈𝒰} E_{ρ∈𝔽₃}[Λ_B(S + ρU)² Ψ_B(S + ρU)] ≤ (95/96) Ψ_B(S)`   (29)
and
`Λ_B(S)² E_{U∈𝒰} E_{ρ∈𝔽₃}[Ψ_B(S + ρU)] ≤ (95/96) Ψ_B(S)`   (30).

**Formalization Note.** \`B ⊆ 𝔽₂ⁿ\` is a nonempty \`Finset\` (the standing "nonempty active set" of §§5.5–5.9) and
the state \`S\` a total function \`𝔽₂ⁿ → ZMod 3\` read on \`B\`. The basis \`X\` of \`V_B*\` is
arbitrary (indexed by any finite type \`ι\`): the statement holds for every basis. \`F₄ = 𝔽₂(ω)\` is
generalized to any field \`K\` of characteristic 2 with \`ω² + ω + 1 = 0\` (every such \`K\` contains
\`𝔽₂(ω) ≅ F₄\`, and all objects are defined over it). Multilinear polynomials are coefficient maps
\`Finset ι → K\`; the zero polynomial has degree \`0\`. The multiset is a family indexed by a nonempty finite type `κ`
(multiplicity = number of indices); each update is given by its extension `L k ∈ V_B*`
(`updOfDual`), so `P_U ∈ N_B(S)` is `L k ∈ Nspace X ω S`. The count hypothesis is multiplied out
by 16. Expectations are uniform averages (`uavg`). -/
theorem lemma_29 (n : ℕ) [NeZero n] (B : Finset (Fin n → ZMod 2)) (hB : B.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    {K : Type*} [Field K] [CharP K 2] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (S : (Fin n → ZMod 2) → ZMod 3) {κ : Type*} [Fintype κ] [Nonempty κ]
    (L : κ → Module.Dual (ZMod 2) (VB B))
    (hcount : 1 ≤ gap X ω S → 16 * {k : κ | L k ∈ Nspace X ω S}.ncard ≤ 9 * Fintype.card κ) :
    uavg (fun k : κ => uavg fun ρ : ZMod 3 =>
        Lambda B (addUpd S ρ (updOfDual (L k))) ^ 2 * Psi X ω (addUpd S ρ (updOfDual (L k)))) ≤
        95 / 96 * Psi X ω S ∧
      Lambda B S ^ 2 * uavg (fun k : κ => uavg fun ρ : ZMod 3 =>
        Psi X ω (addUpd S ρ (updOfDual (L k)))) ≤ 95 / 96 * Psi X ω S := by sorry

end SmallBiasPRF
