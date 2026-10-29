-- Prove2me | Theorems.Thm_SensitivityVariableWord_certificate_iff_word
-- name    : SensitivityVariableWord.certificate_iff_word
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-28T23:51:57.066881+00:00
-- url     : https://prove2.me/theorems/023cdcf0-3e54-4f18-8640-3aeab98be31d
-- title:
--   Canonical all-ones words are complete for variable profile certificates
-- statement:
--   A recursive-profile cycle certificate crossing the 2.15 threshold exists if and only if a canonical all-ones recipe word crosses the same threshold for some valid graph and labeling datum:
--
--   $$
--   \bigl(\exists c:\ R_c>1,\ R_c^{43}<(K_c^{p_c})^{20}\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(\exists G,N,w:\ N>0,\ w\ne[],\ w\text{ admissible},\ H_G(w)^{43}<K_G^{20|w|}\bigr).
--   $$
--
--   Here $K_c$, $p_c$, and $R_c$ are the certificate's vertex count, positive period, and return radius. On the right, $N$ is the state count, $K_G$ is the graph datum's vertex count, and $H_G(w)$ is the word's terminal height clamped below by two.
--
--   On the left, all graph, label, cutoff, recipe, profile, compatibility, and cycle requirements are those of `SensitivityProfileCycle.Certificate`. On the right, the graph datum has exactly the same graph, label, and cutoff requirements. The height is computed by iterating the original transfer followed by interval minimization, starting from the all-ones upper-triangular profile. Recipe validity and tolerance bounds are unchanged.
--
--   All parameters may vary. This equivalence removes free initial and intermediate profile matrices, interval witnesses, and return factors from the existence problem. It does not assert that either side has a witness and does not assert that every Boolean separation must admit such a certificate.
-- source:
--   Original parameter-free canonical-word reduction of SensitivityProfileCycle.Certificate and exists_215_certificate, https://prove2.me/theorems/6c031b2d-eb14-46d2-8d9e-f2db70527660. GraphData copies exactly the graph, labeling, and cutoff fields of https://prove2.me/definitions/6f70ee20-3318-4365-9377-022df0d68b3f. The step uses that module's rawZeroSourceCombined and rawOne without specializing any parameter. The interval envelope, unitProfile, and height come from SensitivityProfileSearch and SensitivityProfileWord; the fixed-parameter normalization theorem is https://prove2.me/theorems/ce0348ca-6a7e-4ada-a2fa-153d9cf45aa3. Underlying recursive bounds: accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and earlier community attribution. No source is claimed to supply a witness reaching 2.15.

import Definitions.Def_SensitivityVariableWord

theorem SensitivityVariableWord.certificate_iff_word :
    (∃ c : SensitivityProfileCycle.Certificate,
      1 < c.radius ∧ c.radius ^ 43 < (c.vertices ^ c.period) ^ 20) ↔
    ∃ (G : SensitivityVariableWord.GraphData) (n : ℕ)
      (word : List (SensitivityProfileCycle.Recipe (n + 1))),
      SensitivityVariableWord.Crosses215 G word := by sorry
