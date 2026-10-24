-- Prove2me | Theorems.Thm_PNPArchive_squareLogTime_subset_NP
-- name    : PNPArchive.squareLogTime_subset_NP
-- status  : Open
-- author  : @xwh
-- created : 2026-10-23T08:41:08.306255+00:00
-- url     : https://prove2.me/theorems/1aeb3277-cfe4-4f5d-b2ce-816195e9bf2c
-- title:
--   Archive target (E)/(U): fixed square-log time is contained in NP
-- statement:
--   This is an **unproved research proposition** from round 79, equation (10), of the P vs NP research archive. It is a proposed sufficient route toward $\mathsf P\ne\mathsf{NP}$; no converse from the separation to this proposition is asserted.
--
--   Put $\ell(n)=\lceil\log_2(n+2)\rceil$ and
--   $$\mathcal T_2=\bigcup_{a\ge1}\operatorname{DTIME}\!\left(2^{a\ell(n)^2}\right).$$
--   The union is over fixed constants. Membership means that one deterministic machine decides the problem on every input, within $C2^{a\ell(n)^2}$ steps, for fixed positive integers $a,C$. The proposed conclusion is
--   $$\boxed{\mathcal T_2\subseteq\mathsf{NP}.}$$
--   Thus each such decision problem should admit one deterministic polynomial-time verifier and a polynomial witness-length bound, chosen independently of the individual input. The statement does not require a polynomial-time witness-search algorithm. The class fixes the square of the logarithm; it is not the union over arbitrary logarithmic powers usually called quasipolynomial time.
--
--   **Exact formal model.** The declaration uses the existing platform definitions `PvsNP_complexity_classes` and their canonical bitstring encodings. A Boolean input word is encoded using three bits per original bit; a Boolean output is a singleton. Time is measured on the actual encoded input. A fixed linear encoding change and polynomial machine-simulation overhead preserve this union over $a,C$. The underlying model is Mathlib's finite-control, finitely many-stack deterministic machine. Although its type permits nominally infinite work alphabets, a fixed program with finite control and finite input alphabet can push only finitely many reachable symbols. The full equivalence to conventional single-tape complexity classes is a mathematical model comparison, not an additional Lean theorem proved by this publication.
--
--   **Connection to the archived route.** In the archive's native three-symbol, two-sided single-tape model, let $D$ consist of valid self-delimiting, zero-padded inputs $x$ whose decoded machine, run on the entire actual string $x$, outputs zero within $T(|x|)=2^{\ell(|x|)^2}$ original steps. Invalid encodings, output one, and timeout are nonmembers. Target (E) asks for one fixed deterministic polynomial-time verifier that rejects every nonmember at every witness length and gives every member a complete witness of length at most $C(|x|+1)^c$.
--
--   Target (U) asks for such absolutely sound static certificates for both canonical answers of every bounded native computation $(M,z,t)$. Define $k=\lceil\log_2(t+2)\rceil$, $s=|\operatorname{code}(M)|+|z|+k+6$, and
--   $$H(s,t)=(s+2)\,2^{\lceil\sqrt{k}\rceil}.$$
--   The full witness, including source binding, all correctness reasons and the original deadline, must have length at most $C H(s,t)^c$. A wrong answer must be rejected for witnesses of every length. Verification time is polynomial in the compact input plus the actual witness length. Correct output one includes output one and failure to output zero by the deadline.
--
--   Round 79 gives a prose normalization argument relating (E), (U), and the displayed inclusion. That argument and its native-to-stack model bridges have not been formalized here. The archive lacks the original decoder source and original PDF/ZIP bytes, so this publication does not pretend to reconstruct their exact parser. It publishes the separate complexity-class formulation explicitly stated in equation (10). The missing multiplication in the extracted typography of $H$ is resolved by round 81's numerical example $s=92,k=65,H=94\cdot512=48,128$.
--
--   **What remains open.** Round 81 supplies an exact matrix-chain certificate mechanism for candidates of controlled width. It does not show that every bounded computation admits one common history representation, variable order, and all source-gate summaries of width $H^{O(1)}$. That universal joint representation bound is a sufficient strategy, not a hypothesis of the theorem above. Restricted width lower bounds do not refute arbitrary reliable certificate systems. Finite tests, hashes, successful runs, interactive soundness with nonzero error, and a favorable transcript do not prove this proposition.
--
--   If the inclusion holds, closure of $\mathcal T_2$ under complement also gives $\mathcal T_2\subseteq\mathsf{NP}\cap\mathsf{coNP}$. The archived diagonal language lies outside $\mathsf P$, so the source's route would imply $\mathsf P\ne\mathsf{NP}$. No converse from $\mathsf P\ne\mathsf{NP}$ to this stronger proposition is claimed. The existing full separation target is https://prove2.me/theorems/31a50e95-7f44-43e6-9c28-50f4610c062a .
--
--   Source: `liushuijixiang/p-vs-np-research-archive`, commit `88a23d510593dc27272d302390f5cf7549b72fc8`, round 79 §§1–4, especially equation (10); rounds 80–81 for failed conversions and the remaining width gap. All 91 archived text files were retrieved and checked against their Git blob hashes. Local compilation checks the definition and unproved declaration only; no proof of this proposition or of P≠NP has been submitted.
-- source:
--   https://github.com/liushuijixiang/p-vs-np-research-archive/blob/88a23d510593dc27272d302390f5cf7549b72fc8/rounds/round-79/report-extracted.md — §§1–4, equation (10); mathematical formulation transcribed from the report, with machine-model comparison explicitly documented.

import Definitions.Def_PNPArchiveSquareLogTime
set_option autoImplicit false

theorem PNPArchive.squareLogTime_subset_NP :
    PNPArchive.SquareLogTime ⊆ PvsNP.NP := by
  sorry
