-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition7
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:39:38.50821+00:00
-- url     : https://prove2.me/theorems/8d5e9299-9311-4c27-b642-1d0cbc6d4653
-- title:
--   proposition-7
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition. Let the target be $\mathrm{id}_d$ with $d\ge2$ and define $\Phi_d=d^{-1}\Gamma(\mathrm{id}_d)$. For each LOCR protocol $\mathcal P$, write $\mathcal S_{\mathcal P}$ for its simulated channel and
--   $$
--   E_F(\mathcal N;\mathcal P)=\operatorname{Tr}\!\left[\Phi_d(\mathrm{id}_R\otimes\mathcal S_{\mathcal P})(\Phi_d)\right],\qquad \dim R=d.
--   $$
--   Then
--   $$
--   e_{\mathrm{LOCR}}^D(\mathcal N)=e_{\mathrm{LOCR}}^F(\mathcal N)=1-\sup_{\mathcal P\in\mathrm{LOCR}}E_F(\mathcal N;\mathcal P).
--   $$
--   Moreover there exists an optimal LOCR protocol whose simulated channel is
--   $$
--   E_F\,\mathrm{id}_d+(1-E_F)\mathcal D_d,\qquad
--   \mathcal D_d(X)=\frac{d\operatorname{Tr}(X)I-X}{d^2-1},
--   $$
--   where $E_F$ is the entanglement fidelity of that optimal protocol, and this protocol attains both operational minimum errors. This connects entanglement fidelity to the optimized worst-case criteria without identifying them by definition.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 13, proposition-7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.13, Proposition 7, (161)–(166): full variational entanglement-fidelity
formula and an attained optimal isotropic simulation, not a definition of worst-case fidelity. -/
theorem proposition7 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond .locr (id : Superop A A) N =
      correctionError .infidelity .locr (id : Superop A A) N ∧
    correctionError .diamond .locr (id : Superop A A) N =
      1 - sSup {v | ∃ P : Superop (A × J) (H × A),
        AllowedCorrection .locr P ∧ v = entFidelity (wire N P)} ∧
    (∃ P : Superop (A × J) (H × A), AllowedCorrection .locr P ∧
      wire N P = (fun X => realOperatorScale (entFidelity (wire N P)) X +
        realOperatorScale (1 - entFidelity (wire N P)) (nonidentityWeylAverage X)) ∧
      simulationErrorFor .diamond (id : Superop A A) (wire N P) =
        correctionError .diamond .locr (id : Superop A A) N ∧
      simulationErrorFor .infidelity (id : Superop A A) (wire N P) =
        correctionError .infidelity .locr (id : Superop A A) N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
