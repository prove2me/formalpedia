-- Prove2me | Theorems.Thm_PPSLattice_theorem_4_13
-- name    : PPSLattice.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:40:29.495594+00:00
-- url     : https://prove2.me/theorems/3e0174a6-65d7-4366-88d4-480c5c4867f3
-- title:
--   Theorem 4.13 — Construction 4.6 is mode indistinguishable
-- statement:
--   Let $(\mathrm{EvalF},\mathrm{EvalFX})$ be polynomial-time homomorphic computation algorithms with properties (1)–(2) for a constant $c$, let the parameters $(n,q,\chi,\tilde\chi,B)$ be valid for $c$ (§4.3), let $K$ be a valid compiler for the circuit of Figure 1 with size $s_C$, let SEPRF be a polynomial-time SEPRF scheme (Definition 4.2) and Garb a polynomial-time blind garbled circuit scheme (Definition 4.4). If the LWE assumption holds for these parameters, then Construction 4.6 satisfies **mode indistinguishability** (Definition 4.1): for every PPT adversary,
--   $$\Bigl|\Pr[\text{mode-indistinguishability experiment}=1]-\tfrac12\Bigr|\le\mathrm{negl}(\lambda).$$
--
--   Differences from the source:
--   - reading: SEPRF satisfies security (Definition 4.2); Garb satisfies security and blindness (Definition 4.4) → F.Efficient ∧ F.IsSEPRF and G.Efficient ∧ G.IsBlindGarb (full definitions, including correctness and the syntax length clauses); reason: Construction 4.6 is built from 'an SEPRF scheme (Definition 4.2)' and 'a blind garble circuit scheme Garb (Definition 4.4)'; the proof uses their correctness (Lemmas 4.16, 4.23) and the reductions run their algorithms
--   - reading: blindness with gk ← Setup(1^λ, 1^s, 1^ℓ) → blindness for every gk in the support of Setup; reason: proof of Lemma 4.22, p.29: 'As blindness holds for every garb.gk and every input A_S'
--   - reading: L, the length of the garbled circuit of C → a function glen(λ, s, ℓ, ℓ_out); CircGarb outputs strings of exactly that length; reason: Construction 4.6 uses L_C̃ in MSKGen before any circuit exists
--   - reading: LWE assumption holds (Assumption 3.4) → LWEHardFor P: every polynomial-time sample count, the distinguisher chooses N first, negligible in λ; reason: the reductions of Lemmas 4.19 and 4.28 learn N from the PPS adversary and use ⌈log N⌉·m (+ λ) samples
--   - generalization: LWE against non-uniform PPT distinguishers (≈c, §3, p.15) → LWE against uniform PPT distinguishers; reason: a weaker hypothesis; the reductions map uniform adversaries to uniform distinguishers
--   - reading: the homomorphic machinery of §3.1, the parameters of §4.3, the circuit of Figure 1 (Claim 4.11) → H.Efficient ∧ H.Valid c, P.Valid c (q prime, n, χ ≥ 1, n = poly(λ, log N), χ = poly(n), parameters computable), FigCompilerValid K sC; reason: these are the ingredients Construction 4.6 is defined from
--   - generalization: χ̃ > λ^{ω(1)} · χ · ⌈log N⌉ · m^{polylog(N)} → for every k, eventually in λ and uniformly in N, λ^k · χ · ⌈log N⌉ · √m · m^{c(d_max(N)+1)} ≤ χ̃; reason: d_max(N) = O(log N), so the printed condition implies this one
--   - generalization: B = χ · χ̃ · ⌈log N⌉ · m^{polylog(N)} → any B with λ^k · λ(4B+2) ≤ q eventually for every k, uniformly in N; reason: security uses B only through λ(4B+2)/q (Lemma 4.20); the printed B is one such value
--   - reading: q > λ^{ω(1)} · λ · (4B+2) → for every k, eventually in λ and uniformly in N, λ^k · λ(4B+2) ≤ q; reason: λ^{ω(1)} is a superpolynomial factor; N is the adversary's choice
--   - reading: Construction 4.6 as printed → construction46 at the level of distributions with an exact discrete Gaussian; ẽ ← [−⌊√m·χ̃⌋, ⌊√m·χ̃⌋]^λ; tg uniform on the allowed residues (point mass at 0 if none); reason: as printed; the integer interval needs a floor
--   - reading: Remark 4.9: x + qr with r ← [0, ⌊2^{ℓq}/q⌋ − 1] sampled by skEnc → one independent r_j per output element of Z_q; reason: the proof of Lemma 4.22 needs independent encodings (statistical distance k·2^{−λ})
--   - reading: D_{Z,σ} with width parameter σ (no formula) → weights exp(−x²/(2σ²)); reason: the convention of [Lyu12], the source of Lemma 3.2
--   - reading: stateful (admissible) PPT adversary → uniform reactive machine RestrictedDec.Adversary (polynomial-time step function, polynomially many coins, bounded state, moves and activations); inadmissible runs scored as a uniform guess; reason: Definitions 4.1, 4.2, 4.4 say PPT adversary; the ½-convention is equivalent to admissibility because an adversary can test its own admissibility
--   - encoding: crs, keys, ciphertexts, messages, set descriptions; [N]; Z_q → bit strings Str (pairs via tup, numbers in binary, least significant bit first); [N] = Finset.Icc 1 N; Z_q = ZMod q; reason: Lean convention; same instances
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.13 (Mode Indistinguishability), p.24

import Mathlib
import Definitions.Def_PPSLattice_construction46
import Definitions.Def_PPSLattice_HomEval_Efficient
import Definitions.Def_PPSLattice_HomEval_Valid
import Definitions.Def_PPSLattice_Params_Valid
import Definitions.Def_PPSLattice_FigCompilerValid
import Definitions.Def_PPSLattice_SEPRF_Efficient
import Definitions.Def_PPSLattice_SEPRF_IsSEPRF
import Definitions.Def_PPSLattice_Garb_Efficient
import Definitions.Def_PPSLattice_Garb_IsBlindGarb
import Definitions.Def_PPSLattice_LWEHardFor
import Definitions.Def_PPSLattice_PPS_ModeInd
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Theorem 4.13** (Mode Indistinguishability). Let `H` be polynomial-time homomorphic computation algorithms satisfying
properties (1)–(2) with constant `c`, `P` valid parameters for `c`, `K` a valid compiler for Figure 1 with size
function `s_C`, `F` a polynomial-time SEPRF scheme (Definition 4.2) and `G` a polynomial-time blind garbled
circuit scheme (Definition 4.4). If the LWE assumption holds for `P`, then Construction 4.6 satisfies
mode indistinguishability (Definition 4.1).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.13, p.24 ("If SEPRF satisfies security property (Definition 4.2), Garb satisfies security and blindness
properties (Definition 4.4), and LWE assumption holds (Assumption 3.4), then Construction 4.6 satisfies
mode indistinguishability property (Definition 4.1)").

**Formalization Note.** The hypotheses on `F` and `G` are the full Definitions 4.2 and 4.4 (correctness
included) together with efficiency: Construction 4.6 is built from "an SEPRF scheme (Definition 4.2)" and
"a blind garble circuit scheme Garb (Definition 4.4)", the proof uses their correctness, and the
reductions run their algorithms. "LWE assumption holds" is `LWEHardFor P`, in which the distinguisher first
chooses `N`. -/
theorem theorem_4_13 (H : HomEval) (c : ℕ) (hHe : H.Efficient) (hH : H.Valid c)
    (P : Params) (hP : P.Valid c) (K : Str → RestrictedDec.Circuit)
    (sC : ℕ → ℕ → ℕ → ℕ → ℕ) (hK : FigCompilerValid K sC)
    (F : SEPRF) (hFe : F.Efficient) (hF : F.IsSEPRF)
    (G : Garb) (hGe : G.Efficient) (hG : G.IsBlindGarb) (hLWE : LWEHardFor P) :
    (construction46 P K sC H F G).ModeInd := by sorry

end PPSLattice
